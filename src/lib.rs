//! An stack array store &T or &mut T as ([TypeId], *const/mut ())
//! Can be used to pass reference to function call when do not have full control of it's argument.
//!
//! # Example:
//! ```rust
//! # use ptr_array::PointerArray;
//! // a determined function that you can't modify for arbitrary argument.
//! fn bar(_arg1: (), mut arg2: PointerArray<'_>) {
//!     // remove &mut Vec<String> from array.
//!     let arg3 = arg2.remove_mut::<Vec<String>>().unwrap();
//!     assert_eq!("arg3", arg3.pop().unwrap());
//! }
//!
//! # fn foo() {
//! let ptr_array = PointerArray::new();
//!
//! let mut arg3 = vec![String::from("arg3")];
//!
//! // insert &mut Vec<String> to array. on Ok(_) the array itself would be returned with
//! // reference successfully inserted.
//! let ptr_array = ptr_array.insert_mut(&mut arg3).unwrap();
//!
//! // pass the array as argument to bar.
//! bar((), ptr_array);
//! # }
//! ```

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

impl Default for PointerArray<'_> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'a, const N: usize> PointerArray<'a, N> {
    /// Construct an empty PointerArray.
    ///
    /// Array have a length of 4usize by default.
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

/// Error type when stack array is full.
pub struct Full<'a, const N: usize>(PointerArray<'a, N>);

impl<'a, const N: usize> Full<'a, N> {
    /// Retrieve array from Error.
    pub fn into_inner(self) -> PointerArray<'a, N> {
        self.0
    }
}

impl<const N: usize> fmt::Debug for Full<'_, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Full(..)")
    }
}

impl<const N: usize> fmt::Display for Full<'_, N> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "PointerArray is full")
    }
}

impl<'a, const N: usize> PointerArray<'a, N> {
    /// Insert a &mut T to array. This method would consume Self.
    ///
    /// If the array have a &mut T already it would replace it and the old one is dropped.
    /// *. only the &mut T would be dropped and destructor of T does not run.
    ///
    /// On Ok(Self) the array with reference successfully inserted would returned.
    /// (Self's lifetime is shrink to the same of input &mut T).
    ///
    /// On Err([Full]) the array without modification would be returned. See [Full::into_inner] for
    /// detail.
    pub fn insert_mut<'b, T: 'static>(
        mut self,
        value: &'b mut T,
    ) -> Result<PointerArray<'b, N>, Full<'a, N>>
    where
        'a: 'b,
    {
        let (id, opt) = self.try_find_one::<T>();

        match opt {
            Some(ptr) => {
                let _ = mem::replace(ptr, value.into());
            }
            None => {
                if self.head == N {
                    return Err(Full(self));
                }
                // SAFETY:
                // head just checked.
                unsafe { self.write(id, value.into()) }
            }
        }

        Ok(self)
    }

    /// The &T version of [Self::insert_mut]. See it for more detail.
    pub fn insert_ref<'b, T: 'static>(
        mut self,
        value: &'b T,
    ) -> Result<PointerArray<'b, N>, Full<'a, N>>
    where
        'a: 'b,
    {
        let (id, opt) = self.try_find_one::<T>();

        match opt {
            Some(ptr) => {
                let _ = mem::replace(ptr, value.into());
            }
            None => {
                if self.head == N {
                    return Err(Full(self));
                }
                // SAFETY:
                // head just checked.
                unsafe { self.write(id, value.into()) }
            }
        }

        Ok(self)
    }

    /// &T version of [Self::remove_mut]. See it for detail.
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

    /// Remove &mut T from array. Return None when there is no according type in array.
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

    /// Get &T without removing it from the array.
    ///
    /// &T can be get from either insert with [Self::insert_mut] or [Self::insert_ref].
    pub fn get<T: 'static>(&self) -> Option<&'a T> {
        let id = TypeId::of::<T>();
        self.try_find_init(&id).and_then(|r| match r {
            RefVariant::Ref(t) => Some(unsafe { &*(*t as *const T) }),
            RefVariant::Mut(t) => Some(unsafe { &*(*t as *mut T as *const T) }),
            RefVariant::None => None,
        })
    }

    /// Get &mut T without removing it from the array.
    ///
    /// &mut T can be get from insert with [Self::insert_mut].
    pub fn get_mut<T: 'static>(&mut self) -> Option<&'a mut T> {
        let id = TypeId::of::<T>();
        self.try_find_init_mut(&id).and_then(|r| match r {
            RefVariant::Mut(t) => Some(unsafe { &mut *(*t as *mut T) }),
            _ => None,
        })
    }

    fn try_find_one<T: 'static>(&mut self) -> (TypeId, Option<&mut RefVariant>) {
        let id = TypeId::of::<T>();
        let opt = self.try_find_init_mut(&id);
        (id, opt)
    }

    fn remove<T, F, R>(&mut self, func: F) -> Option<R>
    where
        T: 'static,
        R: 'a,
        F: for<'r> Fn(&'r mut RefVariant) -> Option<R>,
    {
        let id = TypeId::of::<T>();
        self.try_find_init_mut(&id).and_then(func)
    }

    fn try_find_init(&self, id: &TypeId) -> Option<&RefVariant> {
        self.queue.iter().take(self.head).find_map(|v| {
            // SAFETY:
            // head tracks the items that are initialized and it's safe to assume.
            let (i, opt) = unsafe { v.assume_init_ref() };
            (i == id).then(|| opt)
        })
    }

    fn try_find_init_mut(&mut self, id: &TypeId) -> Option<&mut RefVariant> {
        self.queue.iter_mut().take(self.head).find_map(|v| {
            // SAFETY:
            // head tracks the items that are initialized and it's safe to assume.
            let (i, opt) = unsafe { v.assume_init_mut() };
            (i == id).then(|| opt)
        })
    }

    // SAFETY:
    // Caller must make sure Array is not full and head is not out of bound.
    unsafe fn write(&mut self, id: TypeId, value: RefVariant) {
        self.queue.get_unchecked_mut(self.head).write((id, value));
        self.head += 1;
    }
}

enum RefVariant {
    None,
    Mut(*mut ()),
    Ref(*const ()),
}

impl<T> From<&T> for RefVariant {
    fn from(t: &T) -> Self {
        Self::Ref(t as *const T as *const ())
    }
}

impl<T> From<&mut T> for RefVariant {
    fn from(t: &mut T) -> Self {
        Self::Mut(t as *mut T as *mut ())
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

        let mut map = map
            .insert_mut(&mut s)
            .unwrap()
            .insert_ref(&b)
            .err()
            .unwrap()
            .into_inner();

        assert_eq!(map.remove_mut::<String>().unwrap(), "hello,string!");
    }

    #[test]
    fn ref_variant() {
        let map = PointerArray::<2>::new();

        let mut s = String::from("hello,string!");
        let b = String::from("hello,box!").into_boxed_str();

        let mut map = map.insert_mut(&mut s).unwrap().insert_ref(&b).unwrap();

        assert!(map.remove_ref::<String>().is_none());
        assert!(map.remove_mut::<Box<str>>().is_none());
        assert!(map.remove_mut::<String>().is_some());
        assert!(map.remove_ref::<Box<str>>().is_some());
    }

    #[test]
    fn get() {
        let map = PointerArray::<2>::new();

        let mut s = String::from("hello,string!");
        let b = String::from("hello,box!").into_boxed_str();

        let mut map = map.insert_mut(&mut s).unwrap().insert_ref(&b).unwrap();

        assert!(map.get::<String>().is_some());
        assert!(map.get_mut::<String>().is_some());
        assert!(map.get::<Box<str>>().is_some());
        assert!(map.get_mut::<Box<str>>().is_none());
    }
}
