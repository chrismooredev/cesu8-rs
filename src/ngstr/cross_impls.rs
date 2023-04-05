
use std::borrow::Cow;

use crate::ngstr::prelude::*;

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


// to cow
// can only go one way due to type ownership rules
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


// no CStr == Mutf8CStr -- users should know their CStr's encoding and compare byte slices accordingly

macro_rules! impl_expr_peq {
    ($other:ty, $host:ty, $check:expr) => {
        impl PartialEq<$other> for $host {
            fn eq(&self, other: &$other) -> bool {
                let checkfn: fn(&$host, &$other) -> bool = $check;
                checkfn(self, other)
            }
        }
    };
    (symmetric $other:ty, $host:ty, $check:expr) => {
        impl PartialEq<$other> for $host {
            fn eq(&self, other: &$other) -> bool {
                let checkfn: fn(&$host, &$other) -> bool = $check;
                checkfn(self, other)
            }
        }
        impl PartialEq<$host> for $other {
            fn eq(&self, host: &$host) -> bool {
                let checkfn: fn(&$host, &$other) -> bool = $check;
                checkfn(host, self)
            }
        }
    };
}
impl_expr_peq!(str, Mutf8CStr, |cs, s| s == cs.to_str());
impl_expr_peq!(str, Mutf8Str,  |cs, s| s == cs.to_str());

impl_expr_peq!(symmetric Cesu8Str, Mutf8Str, |cs, ms| cs.to_str() == ms.to_str());
impl_expr_peq!(symmetric Cesu8Str, Mutf8CStr, |cs, mcs| cs.to_str() == mcs.to_str());
impl_expr_peq!(symmetric Mutf8Str, Mutf8CStr, |ms, mcs| ms.to_str() == mcs.to_str());

// TODO: impl SliceIndex<Mutf8CStr> for Range*

