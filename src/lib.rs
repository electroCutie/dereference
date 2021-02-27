use std::{
    boxed::Box,
    marker::PhantomPinned,
    mem::MaybeUninit,
    ops::{Deref, DerefMut},
    pin::Pin,
};

unsafe fn pin_dance<'a, R, T>(pin: &'a mut Pin<R>) -> &'a mut T
where
    R: DerefMut<Target = T>,
{
    let mut_pin = Pin::as_mut(pin);
    Pin::get_unchecked_mut(mut_pin)
}

trait Poly2<A, B> {}

impl<R, T> Poly2<R, T> for Dereference<R, T> {}
impl<R, T> Poly2<R, T> for DereferenceMut<R, T> {}

fn map0<'a, F, FOuterToTn, R, T, Tn, N, DOuter, DInner, Cons, Pinnit>(
    this: Pin<Box<DInner>>,
    referent_fn: F,
    cons: Cons,
    get_t: FOuterToTn,
    pin: Pinnit,
) -> Pin<Box<DOuter>>
where
    F: Fn(Tn) -> N,
    Tn: 'a,
    DInner: Poly2<R, T>,
    FOuterToTn: Fn(&mut DOuter) -> Tn,
    DOuter: Poly2<Box<DInner>, N>,
    Cons: Fn(Box<DInner>) -> Pin<Box<DOuter>>,
    Pinnit: Fn(N, Pin<Box<DOuter>>) -> Pin<Box<DOuter>>,
{
    let rt = unsafe { Pin::into_inner_unchecked(this) };
    let mut d = cons(rt);
    let n = unsafe {
        let mut mut_d = pin_dance(&mut d);
        // This bypasses normal borrow checking
        // We're guaranteeing that the referee lives as long as the produced value and won't be mutated
        referent_fn(get_t(&mut mut_d))
    };
    pin(n, d)
}

fn map_into0<F, R, Rn, T, N, DIn, DOut, GetT, GetR, Pinnit>(
    mut this: Pin<Box<DIn>>,
    referent_fn: F,
    get_t: GetT,
    get_r: GetR,
    pin: Pinnit,
) -> Pin<Box<DOut>>
where
    F: Fn(&Rn, T) -> N,
    DIn: Poly2<R, T>,
    DOut: Poly2<R, N>,
    GetT: Fn(&mut DIn) -> &mut MaybeUninit<Box<T>>,
    GetR: Fn(&DIn) -> &Rn,
    Pinnit: Fn(N, Pin<Box<DOut>>) -> Pin<Box<DOut>>,
{
    unsafe {
        // Get inside the pin
        let mut_ref = pin_dance(&mut this);

        // prepare a landing zone for our current referent
        let mut t = MaybeUninit::uninit();
        // And swap it out for the uninitialized value
        std::mem::swap(&mut t, get_t(mut_ref));
        // And feed it into the user supplied conversion
        let n = referent_fn(get_r(mut_ref), *t.assume_init());

        // Transmute ourselves into the new type
        // This is safe because the referent is boxed so the new type will be the same size as the old one
        // Also we've already de-initialized the referent with the swap, so no incorrectly typed valid memory
        let d_n = std::mem::transmute(this);

        //Install the referent and return
        pin(n, d_n)
    }
}

pub struct Dereference<R, T> {
    referent: MaybeUninit<Box<T>>,
    referee: R, // Must come second for drop order to be safe
    _pin: PhantomPinned,
}

impl<R, T> Dereference<R, T> {
    fn new0(referee: R) -> Pin<Box<Self>> {
        Box::pin(Dereference {
            referee,
            referent: MaybeUninit::uninit(),
            _pin: PhantomPinned,
        })
    }

    fn pinnit(t: T, mut this: Pin<Box<Self>>) -> Pin<Box<Self>> {
        unsafe {
            pin_dance(&mut this).referent = MaybeUninit::new(Box::new(t));
        }

        this
    }

    pub fn new<'a, F>(referee: R, referent_fn: F) -> Pin<Box<Self>>
    where
        R: 'a,
        F: Fn(&'a R) -> T,
    {
        let d = Self::new0(referee);
        let t = unsafe {
            // This bypasses normal borrow checking
            // We're guaranteeing that the referee lives as long as the produced value and won't be mutated
            let r_ptr: *const R = &d.referee;
            referent_fn(&*r_ptr)
        };
        Self::pinnit(t, d)
    }

    pub fn map<'a, F, N>(
        this: Pin<Box<Self>>,
        referent_fn: F,
    ) -> Pin<Box<Dereference<Box<Self>, N>>>
    where
        Self: 'a,
        F: Fn(&'a T) -> N,
    {
        map0(
            this,
            referent_fn,
            Dereference::new0,
            |m_d| unsafe { &*m_d.referee.referent.as_ptr() },
            Dereference::pinnit,
        )
    }

    pub fn map_mut<'a, F, N>(
        this: Pin<Box<Self>>,
        referent_fn: F,
    ) -> Pin<Box<DereferenceMut<Box<Self>, N>>>
    where
        Self: 'a,
        F: Fn(&'a mut T) -> N,
    {
        map0(
            this,
            referent_fn,
            DereferenceMut::new0,
            |m_d| unsafe { &mut *m_d.referee.referent.as_mut_ptr() },
            DereferenceMut::pinnit,
        )
    }

    pub fn map_into<'a, F, N>(this: Pin<Box<Self>>, referent_fn: F) -> Pin<Box<Dereference<R, N>>>
    where
        Self: 'a,
        F: Fn(&R, T) -> N,
    {
        map_into0(
            this,
            referent_fn,
            |m_r| &mut m_r.referent,
            |m_r| &m_r.referee,
            Dereference::pinnit,
        )
    }

    pub fn ref_referee(&self) -> &R {
        &self.referee
    }
}

impl<R, T> Deref for Dereference<R, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // safety guranteed by construction
        unsafe { &*self.referent.as_ptr() }
    }
}

impl<R, T> DerefMut for Dereference<R, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // safety guranteed by construction
        unsafe { &mut *self.referent.as_mut_ptr() }
    }
}

impl<R, T> Drop for Dereference<R, T> {
    fn drop(&mut self) {
        let mut t = MaybeUninit::uninit();
        std::mem::swap(&mut t, &mut self.referent);
        std::mem::forget(t);
    }
}

/* Mutable Variant (cannot borrow referee externally) */

pub struct DereferenceMut<R, T> {
    referent: MaybeUninit<Box<T>>,
    referee: R, // Must come second for drop order to be safe
    _pin: PhantomPinned,
}

impl<R, T> DereferenceMut<R, T> {
    fn new0(referee: R) -> Pin<Box<Self>> {
        Box::pin(DereferenceMut {
            referee,
            referent: MaybeUninit::uninit(),
            _pin: PhantomPinned,
        })
    }

    fn pinnit(t: T, mut this: Pin<Box<Self>>) -> Pin<Box<Self>> {
        unsafe {
            pin_dance(&mut this).referent = MaybeUninit::new(Box::new(t));
        }

        this
    }

    pub fn new_mut<'a, F>(referee: R, referentr_fn: F) -> Pin<Box<Self>>
    where
        R: 'a,
        F: Fn(&'a mut R) -> T,
    {
        let mut d = Self::new0(referee);
        unsafe {
            let mut_d = pin_dance(&mut d);
            let r_ptr: *mut R = &mut mut_d.referee;
            mut_d.referent = MaybeUninit::new(Box::new(referentr_fn(&mut *r_ptr)));
        };

        d
    }

    pub fn map_mut<'a, F, N>(
        this: Pin<Box<Self>>,
        referent_fn: F,
    ) -> Pin<Box<DereferenceMut<Box<Self>, N>>>
    where
        Self: 'a,
        F: Fn(&'a mut T) -> N,
    {
        map0(
            this,
            referent_fn,
            DereferenceMut::new0,
            |m_d| unsafe { &mut *m_d.referee.referent.as_mut_ptr() },
            DereferenceMut::pinnit,
        )
    }

    pub fn map<F, N>(this: Pin<Box<Self>>, referent_fn: F) -> Pin<Box<Dereference<Box<Self>, N>>>
    where
        F: Fn(&T) -> N,
    {
        map0(
            this,
            referent_fn,
            Dereference::new0,
            |m_d| unsafe { &*m_d.referee.referent.as_ptr() },
            Dereference::pinnit,
        )
    }

    pub fn map_into<'a, F, N>(
        this: Pin<Box<Self>>,
        referent_fn: F,
    ) -> Pin<Box<DereferenceMut<R, N>>>
    where
        Self: 'a,
        F: Fn(T) -> N,
    {
        map_into0(
            this,
            |_: &(), x| referent_fn(x),
            |m_r| &mut m_r.referent,
            |_| &(),
            DereferenceMut::pinnit,
        )
    }
}

impl<R, T> Deref for DereferenceMut<R, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        // safety guranteed by construction
        unsafe { &*self.referent.as_ptr() }
    }
}

impl<R, T> DerefMut for DereferenceMut<R, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        // safety guranteed by construction
        unsafe { &mut *self.referent.as_mut_ptr() }
    }
}

impl<R, T> Drop for DereferenceMut<R, T> {
    fn drop(&mut self) {
        let mut t = MaybeUninit::uninit();
        std::mem::swap(&mut t, &mut self.referent);
        std::mem::forget(t);
    }
}

#[cfg(test)]
mod tests {
    use std::ops::Deref;

    use super::*;
    #[test]
    fn it_works() {
        let a = Dereference::new(0, |z| (z, 0));
        let b = Dereference::map_mut(a, |x: &mut (&i32, i32)| {
            x.1 = 1;
            (x, 2)
        });

        let ((x, y), z) = DereferenceMut::deref(&b);
        assert_eq!(**x, 0);
        assert_eq!(*y, 1);
        assert_eq!(*z, 2);
    }

    #[test]
    fn into_works() {
        let a = Dereference::new(0, |z| (z, 0));
        let b = Dereference::map_into(a, |_, mut x: (&i32, i32)| {
            x.1 = 1;
            (x, 2u64)
        });

        let ((x, y), z) = Dereference::deref(&b);
        assert_eq!(**x, 0);
        assert_eq!(*y, 1);
        assert_eq!(*z, 2);
    }
}
