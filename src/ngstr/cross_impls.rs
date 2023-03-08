
use std::borrow::Cow;
use std::ops::{Add, AddAssign};

use crate::ngstr::*;

macro_rules! impl_expr_from {
    ($($lt:lifetime),*; $from:ty, $to:ty, $map:expr) => {
        impl<$($lt),*> From<$from> for $to {
            fn from(value: $from) -> Self {
                let mapfn: fn($from) -> Self = $map;
                mapfn(value)
            }
        }
    };
    ($from:ty, $to:ty, $map:expr) => {
        impl_expr_from!(; $from, $to, $map);
    };
    (bi $($lt:lifetime),*; $from:ty, $to:ty, $forward:expr, $backward:expr) => {
        impl_expr_from!($($lt),*; $from, $to, $forward);
        impl_expr_from!($($lt),*; $to, $from, $backward);
    };
    // (cow $borrowed:ty)

    (cow $local:ty, $local_owned:ty, $other:ty, $other_owned:ty, $forward_borrowed:expr, $forward_owned:expr, $backward_borrowed:expr, $backward_owned:expr) => {
        impl_expr_from!('a; &'a $local, Cow<'a, $other>, $forward_borrowed);
        impl_expr_from!($local_owned, Cow<'static, $other>, $forward_owned);
    };
}

impl_expr_from!(String, Mutf8CString, Mutf8CString::from_utf8);
impl_expr_from!(Mutf8CString, String, Mutf8CString::into_string);

// to cow
impl_expr_from!('a; Mutf8String, Cow<'a, str>, |s| Cow::Owned(Mutf8String::into_string(s)));
impl_expr_from!('a; Mutf8CString, Cow<'a, str>, |s| Cow::Owned(Mutf8CString::into_string(s)));
impl_expr_from!('a; &'a Mutf8CStr, Cow<'a, CStr>, |s| Cow::Borrowed(Mutf8CStr::as_cstr(s)));
impl_expr_from!('a; Mutf8CString, Cow<'a, CStr>, |s| Cow::Owned(Mutf8CString::into_cstring(s)));
impl_expr_from!('a; &'a Mutf8Str, Cow<'a, [u8]>, |s| Cow::Borrowed(Mutf8Str::as_bytes(s)));
impl_expr_from!('a; Mutf8String, Cow<'a, [u8]>, |s| Cow::Owned(Mutf8String::into_bytes(s)));

impl_expr_from!(Box<Mutf8CStr>, Box<[u8]>, |s: Box<Mutf8CStr>| {
    let raw = Box::into_raw(s);
    // SAFETY: Mutf8CStr is internally just [u8]
    // see stdlib's From<Box<str>> for Box<[u8]>
    unsafe { Box::from_raw(raw as *mut [u8]) }
});


// no CStr == Mutf8CStr -- users should detect their CStr's encoding and compare byte slices

macro_rules! impl_expr_peq {
    ($other:ty, $host:ty, $check:expr) => {
        impl PartialEq<$other> for $host {
            fn eq(&self, other: &$other) -> bool {
                let checkfn: fn(&$host, &$other) -> bool = $check;
                checkfn(self, other)
            }
        }
    }
}
impl_expr_peq!(str, Mutf8CStr, |cs, s| s == cs.to_str());
impl_expr_peq!(str, Mutf8Str,  |cs, s| s == cs.to_str());
impl_expr_peq!(CStr, Mutf8CStr, |cs, s| s.to_bytes() == cs.as_bytes());
impl_expr_peq!(CStr, Mutf8Str,  |cs, s| s.to_bytes() == cs.as_bytes());

// TODO: impl SliceIndex<Mutf8CStr> for Range*

impl<'a> Add<&'a Mutf8CStr> for Cow<'a, Mutf8CStr> {
    type Output = Cow<'a, Mutf8CStr>;
    fn add(self, rhs: &'a Mutf8CStr) -> Cow<'a, Mutf8CStr> {
        if rhs.is_empty() {
            self
        } else {
            let mut o = self.into_owned();
            o.extend_from_mutf8(rhs);
            Cow::Owned(o)
        }
    }
}

impl Add<&Mutf8CStr> for Mutf8CString {
    type Output = Mutf8CString;
    fn add(mut self, rhs: &Mutf8CStr) -> Self::Output {
        self.extend_from_mutf8(rhs);
        self
    }
}
impl Add<&str> for Mutf8CString {
    type Output = Mutf8CString;
    fn add(mut self, rhs: &str) -> Self::Output {
        self.extend_from_str(rhs);
        self
    }
}
impl AddAssign<&Mutf8CStr> for Mutf8CString {
    fn add_assign(&mut self, rhs: &Mutf8CStr) {
        self.extend_from_mutf8(rhs);
    }
}
impl AddAssign<&str> for Mutf8CString {
    fn add_assign(&mut self, rhs: &str) {
        self.extend_from_str(rhs);
    }
}

