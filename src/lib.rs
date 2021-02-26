use std::marker::PhantomPinned;
use std::mem::MaybeUninit;
use std::{
    boxed::Box,
    ops::{Deref, DerefMut},
    pin::Pin,
};

pub struct Dereference<R, T> {
    referee: R,
    referent: MaybeUninit<T>,
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
            let mut_pin = Pin::as_mut(&mut this);
            Pin::get_unchecked_mut(mut_pin).referent = MaybeUninit::new(t);
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

    pub fn chain<'a, F, N>(
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

    pub fn chain_mut<'a, F, N>(this: Pin<Box<Self>>, referentr_fn: F) -> Pin<Box<DereferenceMut<Pin<Box<Self>>, N>>>
    where
        Self: 'a,
        F: Fn(&'a mut T) -> N,
    {
        let mut d = DereferenceMut::new0(this);

        unsafe {
            let mut_pin = Pin::as_mut(&mut d);
            let mut_d = Pin::get_unchecked_mut(mut_pin);
            
            let mut_self = Pin::as_mut(&mut mut_d.referee);
            let t_ptr = Pin::get_unchecked_mut(mut_self).referent.as_mut_ptr();
            mut_d.referent = MaybeUninit::new(referentr_fn(&mut *t_ptr));
        };

        d
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
    referee: R,
    referent: MaybeUninit<T>,
    _pin: PhantomPinned,
}

impl<R, T> DereferenceMut<R, T> {
    fn new0(referee: R) -> Pin<Box<Self>>{
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
            let mut_pin = Pin::as_mut(&mut d);
            let mut_d = Pin::get_unchecked_mut(mut_pin);
            let r_ptr: *mut R = &mut mut_d.referee;
            mut_d.referent = MaybeUninit::new(referentr_fn(&mut *r_ptr));
        };

        d
    }

    pub fn chain_mut<'a, F, N>(self, referentr_fn: F) -> Pin<Box<DereferenceMut<Self, N>>>
    where
        Self: 'a,
        F: Fn(&'a mut T) -> N,
    {
        let mut d = DereferenceMut::new0(self);

        unsafe {
            let mut_pin = Pin::as_mut(&mut d);
            let mut_d = Pin::get_unchecked_mut(mut_pin);
            let t_ptr: *mut T = mut_d.referee.deref_mut();
            mut_d.referent = MaybeUninit::new(referentr_fn(&mut *t_ptr));
        };

        d
    }

    pub fn chain<F, N>(self, referentr_fn: F) -> Pin<Box<Dereference<Self, N>>>
    where
        F: Fn(& T) -> N,
    {
        let mut d = Dereference::new0(self);

        let t = referentr_fn(d.referee.deref());
        unsafe {
            let mut_pin = Pin::as_mut(&mut d);
            Pin::get_unchecked_mut(mut_pin).referent = MaybeUninit::new(t);
        };

        d
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
        let a = //
            Dereference::new(0, |z| (z, 0));
        let b = //
            Dereference::chain_mut(a, |x: &mut (&i32, i32)| {
                x.1 = 1;
                (x, 2)
            });

        let ((x, y), z) = DereferenceMut::deref(&b);
        assert_eq!(**x, 0);
        assert_eq!(*y, 1);
        assert_eq!(*z, 2);
    }
}
