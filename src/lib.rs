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
    ) -> Pin<Box<Dereference<Pin<Box<Self>>, N>>>
    where
        Self: 'a,
        F: Fn(&'a T) -> N,
    {
        let d = Dereference::new0(this);
        let n = unsafe {
            // This bypasses normal borrow checking
            // We're guaranteeing that the referee lives as long as the produced value and won't be mutated
            referent_fn(&*d.referee.referent.as_ptr())
        };
        Dereference::pinnit(n, d)
    }

    pub fn map_mut<'a, F, N>(
        this: Pin<Box<Self>>,
        referentr_fn: F,
    ) -> Pin<Box<DereferenceMut<Pin<Box<Self>>, N>>>
    where
        Self: 'a,
        F: Fn(&'a mut T) -> N,
    {
        let mut d = DereferenceMut::new0(this);

        unsafe {
            let mut_d = pin_dance(&mut d);
            let t_ptr = pin_dance(&mut mut_d.referee).referent.as_mut_ptr();

            mut_d.referent = MaybeUninit::new(Box::new(referentr_fn(&mut *t_ptr)));
        };

        d
    }

    pub fn map_into<'a, F, N>(mut this: Pin<Box<Self>>, referent_fn: F) -> Pin<Box<Dereference<T, N>>>
    where
        Self: 'a,
        F: Fn(&R, T) -> N,
    {
        unsafe {
            // Get inside the pin
            let mut_ref = pin_dance(&mut this);

            // prepare a landing zone for our current referent
            let mut t = MaybeUninit::uninit();
            // And swap it out for the uninitialized value
            std::mem::swap(&mut t, &mut mut_ref.referent);
            // And feed it into the user supplied conversion
            let n = referent_fn(&mut_ref.referee, *t.assume_init());

            // Transmute ourselves into the new type
            // This is safe because the referent is boxed so the new type will be the same size as the old one
            // Also we've already de-initialized the referent with the swap, so no incorrectly typed valid memory
            let mut dn = std::mem::transmute(this);

            // Pin dance with the transmuated type
            let mut_ref: &mut Dereference<T, N> = pin_dance(&mut dn);
            //And give it the new refferent
            mut_ref.referent = MaybeUninit::new(Box::new(n));

            dn
        }
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

    pub fn map_mut<'a, F, N>(self, referentr_fn: F) -> Pin<Box<DereferenceMut<Self, N>>>
    where
        Self: 'a,
        F: Fn(&'a mut T) -> N,
    {
        let mut d = DereferenceMut::new0(self);

        unsafe {
            let mut_d = pin_dance(&mut d);
            let t_ptr: *mut T = DereferenceMut::deref_mut(&mut mut_d.referee);
            mut_d.referent = MaybeUninit::new(Box::new(referentr_fn(&mut *t_ptr)));
        };

        d
    }

    pub fn map<F, N>(self, referentr_fn: F) -> Pin<Box<Dereference<Self, N>>>
    where
        F: Fn(&T) -> N,
    {
        let mut d = Dereference::new0(self);

        let t = referentr_fn(d.referee.deref());
        unsafe {
            pin_dance(&mut d).referent = MaybeUninit::new(Box::new(t));
        };

        d
    }

    pub fn map_into<'a, F, N>(
        mut this: Pin<Box<Self>>,
        referent_fn: F,
    ) -> Pin<Box<DereferenceMut<T, N>>>
    where
        Self: 'a,
        F: Fn(T) -> N,
    {
        unsafe {
            // Get inside the pin
            let mut_ref = pin_dance(&mut this);

            // prepare a landing zone for our current referent
            let mut t = MaybeUninit::uninit();
            // And swap it out for the uninitialized value
            std::mem::swap(&mut t, &mut mut_ref.referent);
            // And feed it into the user supplied conversion
            let n = referent_fn(*t.assume_init());

            // Transmute ourselves into the new type
            // This is safe because the referent is boxed so the new type will be the same size as the old one
            // Also we've already de-initialized the referent with the swap, so no incorrectly typed valid memory
            let mut dn = std::mem::transmute(this);

            // Pin dance with the transmuated type
            let mut_ref: &mut DereferenceMut<T, N> = pin_dance(&mut dn);
            //And give it the new refferent
            mut_ref.referent = MaybeUninit::new(Box::new(n));

            dn
        }
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
