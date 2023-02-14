
use std::borrow::Cow;
use std::ops::{Add, AddAssign};

use crate::*;

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
}

impl_expr_from!(String, Mutf8CString, Mutf8CString::from_string);
impl_expr_from!(Mutf8CString, String, Mutf8CString::into_string);
impl_expr_from!(Box<Mutf8CStr>, Mutf8CString, Mutf8CString::from_boxed_mutf8c);
impl_expr_from!('a; &'a Mutf8CStr, Cow<'a, str>, Mutf8CStr::to_string);


// no CStr == Mutf8CStr -- users should detect their CStr's encoding and compare byte slices
impl PartialEq<str> for Mutf8CStr {
    fn eq(&self, other: &str) -> bool {
        other == self.to_string()
    }
}

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
