#![no_std]

use core::{
    any::TypeId,
    fmt,
    hint::unreachable_unchecked,
    marker::PhantomData,
    mem::{self, MaybeUninit},
};

pub struct PointerArray<'a, const N: usize = 4> {
    queue: [MaybeUninit<(TypeId, RefVariant)>; N],
    head: usize,
    _marker: PhantomData<&'a ()>,
}

enum RefVariant {
    None,
    Mut(*mut ()),
    Ref(*const ()),
}

impl Default for PointerArray<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, const N: usize> PointerArray<'a, N> {
    pub const fn new() -> Self {
        PointerArray {
            // SAFETY:
            // [MaybeUninit<T>; N] is safe to assume from uninit.
            queue: unsafe { MaybeUninit::uninit().assume_init() },
            head: 0,
            _marker: PhantomData,
        }
    }
}

pub struct Full<'a, const N: usize>(PointerArray<'a, N>);

impl<'a, const N: usize> Full<'a, N> {
    pub fn into_inner(self) -> PointerArray<'a, N> {
        self.0
    }
}

impl<const N: usize> fmt::Debug for Full<'_, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PointerMap is full")
    }
}

impl<'a, const N: usize> PointerArray<'a, N> {
    pub fn insert_mut<'b, T: 'static>(
        mut self,
        value: &'b mut T,
    ) -> Result<PointerArray<'b, N>, Full<'a, N>>
    where
        'a: 'b,
    {
        if self.queue.len() == self.head {
            return Err(Full(self));
        }

        let (id, opt) = self.try_find_one::<T>();

        match opt {
            Some(ptr) => {
                let _ = mem::replace(ptr, RefVariant::Mut(value as *mut T as *mut ()));
            }
            None => {
                self.queue[self.head].write((id, RefVariant::Mut(value as *mut T as *mut ())));
                self.head += 1;
            }
        }

        Ok(self)
    }

    pub fn insert_ref<'b, T: 'static>(
        mut self,
        value: &'b T,
    ) -> Result<PointerArray<'b, N>, Full<'a, N>>
    where
        'a: 'b,
    {
        if self.queue.len() == self.head {
            return Err(Full(self));
        }

        let (id, opt) = self.try_find_one::<T>();

        match opt {
            Some(ptr) => {
                let _ = mem::replace(ptr, RefVariant::Ref(value as *const T as *const ()));
            }
            None => {
                self.queue[self.head].write((id, RefVariant::Ref(value as *const T as *const ())));
                self.head += 1;
            }
        }

        Ok(self)
    }

    pub fn remove_ref<T: 'static>(&mut self) -> Option<&'a T> {
        self.remove::<T, _, _>(|r| match r {
            RefVariant::Ref(_) => match mem::replace(r, RefVariant::None) {
                RefVariant::Ref(t) => Some(unsafe { &*(t as *const T) }),
                // SAFETY:
                // The branch was just checked before.
                _ => unsafe { unreachable_unchecked() },
            },
            _ => None,
        })
    }

    pub fn remove_mut<T: 'static>(&mut self) -> Option<&'a mut T> {
        self.remove::<T, _, _>(|r| match r {
            RefVariant::Mut(_) => match mem::replace(r, RefVariant::None) {
                RefVariant::Mut(t) => Some(unsafe { &mut *(t as *mut T) }),
                // SAFETY:
                // The branch was just checked before.
                _ => unsafe { unreachable_unchecked() },
            },
            _ => None,
        })
    }

    fn try_find_one<T: 'static>(&mut self) -> (TypeId, Option<&mut RefVariant>) {
        let id = TypeId::of::<T>();
        let opt = self.try_find_init(&id);
        (id, opt)
    }

    fn remove<T, F, R>(&mut self, func: F) -> Option<R>
    where
        T: 'static,
        R: 'a,
        F: for<'r> Fn(&'r mut RefVariant) -> Option<R>,
    {
        let id = TypeId::of::<T>();
        self.try_find_init(&id).and_then(func)
    }

    fn try_find_init(&mut self, id: &TypeId) -> Option<&mut RefVariant> {
        self.queue.iter_mut().take(self.head).find_map(|v| {
            // SAFETY:
            // head tracks the items that are initialized and it's safe to assume.
            let (i, opt) = unsafe { v.assume_init_mut() };
            (i == id).then(|| opt)
        })
    }
}

#[cfg(test)]
mod test {
    use super::*;

    extern crate alloc;

    use alloc::{boxed::Box, string::String, vec, vec::Vec};

    #[test]
    fn test() {
        let map = PointerArray::default();

        let mut s = String::from("hello,string!");

        let s2 = String::from("hello,box!").into_boxed_str();

        let map = map.insert_mut(&mut s).unwrap();

        let map = map.insert_ref(&s2).unwrap();

        fn scope(mut map: PointerArray<'_>) {
            let s2 = map.remove_ref::<Box<str>>().unwrap();

            let mut v = vec![String::from("hello,string!")];

            let s = map.remove_mut::<String>().unwrap();

            let mut map = map.insert_mut(&mut v).unwrap();

            assert_eq!(s, "hello,string!");

            let v = map.remove_mut::<Vec<String>>().unwrap();

            assert_eq!(s, &v.pop().unwrap());

            assert_eq!(&**s2, "hello,box!");
        }

        assert_eq!(&*s2, "hello,box!");

        scope(map);

        assert_eq!(s, "hello,string!");
    }

    #[test]
    fn out_of_bound() {
        let map = PointerArray::<1>::new();

        let mut s = String::from("hello,string!");

        let b = String::from("hello,box!").into_boxed_str();

        let map = map.insert_mut(&mut s).unwrap();

        assert!(map.insert_ref(&b).is_err());
    }

    #[test]
    fn error_retake() {
        let map = PointerArray::<1>::new();

        let mut s = String::from("hello,string!");

        let b = String::from("hello,box!").into_boxed_str();

        let map = map.insert_mut(&mut s).unwrap();

        let mut map = map.insert_ref(&b).err().unwrap().into_inner();

        assert_eq!(map.remove_mut::<String>().unwrap(), "hello,string!");
    }

    #[test]
    fn ref_variant() {
        let map = PointerArray::<2>::new();

        let mut s = String::from("hello,string!");

        let b = String::from("hello,box!").into_boxed_str();

        let map = map.insert_mut(&mut s).unwrap();

        let mut map = map.insert_ref(&b).unwrap();

        assert!(map.remove_ref::<String>().is_none());
        assert!(map.remove_mut::<Box<str>>().is_none());
        assert!(map.remove_mut::<String>().is_some());
        assert!(map.remove_ref::<Box<str>>().is_some());
    }
}
