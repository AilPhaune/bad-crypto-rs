use std::{fmt::Debug, marker::PhantomData};

use rug::{Integer, integer::IsPrime};

pub mod modular;
pub mod poly;

pub trait Group<T: Debug>: Debug {
    /// The additive identity element `0`
    fn additive_identity(&self) -> T;

    /// Checks if `x` is the additive identity
    fn is_additive_identity(&self, x: &T) -> bool;

    /// The additive inverse of `x`
    fn additive_inverse(&self, x: &T) -> T;

    /// Addition of `x` and `y`
    fn add(&self, x: &T, y: &T) -> T;

    /// The smallest integer n such that for all element x of the group, n * x = 0, None if there is no such integer or if it is uncomputable
    fn group_exponent(&self) -> Option<Integer>;

    /// Subtraction of `x` and `y`
    fn sub(&self, x: &T, y: &T) -> T {
        self.add(x, &self.additive_inverse(y))
    }

    /// Checks if this group and another group are equals
    fn eq_group(&self, other: &Self) -> bool;

    /// Equality of `x` and `y`
    fn eq(&self, x: &T, y: &T) -> bool;

    /// Clones `x`
    fn clone(&self, x: &T) -> T;

    /// Repeated addition of `x` `n` times
    fn repeated_addition(&self, x: T, n: &Integer) -> T {
        if n.is_zero() {
            return self.additive_identity();
        } else if *n < 0 {
            return self.repeated_addition(self.additive_inverse(&x), &n.as_neg());
        }

        let mut result = self.additive_identity();

        for i in (0..n.significant_bits()).rev() {
            result = self.add(&result, &result);
            if n.get_bit(i) {
                result = self.add(&result, &x);
            }
        }

        result
    }
}

pub trait Ring<T: Debug>: Group<T> {
    /// The multiplicative identity element `1`
    fn multiplicative_identity(&self) -> T;

    /// Multiplication of `x` and `y`
    fn mul(&self, x: &T, y: &T) -> T;

    /// Exponentiation of `x` by `n`, where `n` is a positive integer
    fn power(&self, x: &T, n: &Integer) -> Option<T> {
        if n.is_zero() {
            return Some(self.multiplicative_identity());
        } else if *n < 0 {
            return None;
        }

        let mut result = self.multiplicative_identity();

        for i in (0..n.significant_bits()).rev() {
            result = self.mul(&result, &result);
            if n.get_bit(i) {
                result = self.mul(&result, x);
            }
        }

        Some(result)
    }

    /// The smallest positive integer n such that for all non-zero element x of the ring, x^n = 1, None if there is no such integer or if it is uncomputable
    fn ring_exponent(&self) -> Option<Integer>;

    /// Checks if this ring and another ring are equals
    fn eq_ring(&self, other: &Self) -> bool;
}

pub trait CompleteRing<T: Debug>: Ring<T> {
    /// The multiplicative inverse of `x`
    fn multiplicative_inverse(&self, x: &T) -> Option<T>;
}

pub trait Field<T: Debug, NZ: Debug>: CompleteRing<T> {
    /// Constructs an instance of a non zero field element
    fn construct_non_zero(&self, x: T) -> Option<NZ>;

    /// Checks if this field is equal to another field
    fn eq_field(&self, other: &Self) -> bool;

    /// Deconstructs a non zero field element
    fn deconstruct_non_zero(&self, x: NZ) -> T;

    /// Constructs an instance of a non zero field element
    fn get_non_zero(&self, x: &T) -> Option<NZ>;

    /// Deconstructs a non zero field element
    fn get_element_from_non_zero(&self, x: &NZ) -> T;

    /// Division of `x` and `y`
    fn div(&self, x: &T, y: &NZ) -> T;

    /// The field's characteristic
    fn characteristic(&self) -> Integer;
}

pub trait FiniteField<T: Debug, NZ: Debug, U: Debug>: Field<T, NZ> {
    /// The number of elements of the field
    fn order(&self) -> U;
}

pub trait HasAdditiveIdentity: Debug {
    fn additive_identity() -> Self;
}

pub trait HasMultiplicativeIdentity: Debug {
    fn multiplicative_identity() -> Self;
}

pub trait CheckIsPrime: HasAdditiveIdentity + HasMultiplicativeIdentity {
    fn is_prime(&self) -> IsPrime;
}

macro_rules! is_prime_impl {
    ($t: ty) => {
        impl HasAdditiveIdentity for $t {
            fn additive_identity() -> Self {
                0
            }
        }

        impl HasMultiplicativeIdentity for $t {
            fn multiplicative_identity() -> Self {
                1
            }
        }

        impl CheckIsPrime for $t {
            fn is_prime(&self) -> IsPrime {
                let i: Integer = (*self).into();
                i.is_probably_prime(100)
            }
        }
    };
}

is_prime_impl! { u8 }
is_prime_impl! { u16 }
is_prime_impl! { u32 }
is_prime_impl! { u64 }
is_prime_impl! { u128 }

is_prime_impl! { i8 }
is_prime_impl! { i16 }
is_prime_impl! { i32 }
is_prime_impl! { i64 }
is_prime_impl! { i128 }

is_prime_impl! { usize }
is_prime_impl! { isize }

impl HasAdditiveIdentity for Integer {
    fn additive_identity() -> Self {
        0.into()
    }
}

impl HasMultiplicativeIdentity for Integer {
    fn multiplicative_identity() -> Self {
        1.into()
    }
}

impl CheckIsPrime for Integer {
    fn is_prime(&self) -> IsPrime {
        self.is_probably_prime(100)
    }
}

#[derive(Debug)]
pub struct Fraction<T: Debug, NZ: Debug, F: Field<T, NZ>> {
    _phantom: PhantomData<(NZ, F)>,
    num: T,
    den: T,
}

impl<T: Debug, NZ: Debug, F: Field<T, NZ>> Fraction<T, NZ, F> {
    pub fn new(num: T, den: T) -> Fraction<T, NZ, F> {
        Fraction {
            _phantom: PhantomData,
            num,
            den,
        }
    }

    pub fn is_zero(&self, field: &F) -> bool {
        field.is_additive_identity(&self.num)
    }

    pub fn mul(&self, other: &Fraction<T, NZ, F>, field: &F) -> Fraction<T, NZ, F> {
        Fraction::new(
            field.mul(&self.num, &other.num),
            field.mul(&self.den, &other.den),
        )
    }

    pub fn div(&self, other: &Fraction<T, NZ, F>, field: &F) -> Fraction<T, NZ, F> {
        Fraction::new(
            field.mul(&self.num, &other.den),
            field.mul(&self.den, &other.num),
        )
    }

    pub fn inv(&self, field: &F) -> Fraction<T, NZ, F> {
        Fraction::new(field.clone(&self.den), field.clone(&self.num))
    }

    pub fn invert(&mut self) {
        std::mem::swap(&mut self.num, &mut self.den);
    }

    pub fn get_num(&self) -> &T {
        &self.num
    }

    pub fn get_den(&self) -> &T {
        &self.den
    }

    pub fn add(&self, other: &Fraction<T, NZ, F>, field: &F) -> Fraction<T, NZ, F> {
        // a/b + c/d = ad/bd + bc/ab = (ad + bc)/(bd)
        let ad = field.mul(&self.num, &other.den);
        let bc = field.mul(&self.den, &other.num);
        let bd = field.mul(&self.den, &other.den);
        Fraction::new(field.add(&ad, &bc), bd)
    }

    pub fn neg(&self, field: &F) -> Fraction<T, NZ, F> {
        Fraction::new(field.additive_inverse(&self.num), field.clone(&self.den))
    }

    pub fn negate(&mut self, field: &F) {
        self.num = field.additive_inverse(&self.num);
    }

    pub fn sub(&self, other: &Fraction<T, NZ, F>, field: &F) -> Fraction<T, NZ, F> {
        // a/b - c/d = ad/bd - bc/ab = (ad - bc)/(bd)
        let ad = field.mul(&self.num, &other.den);
        let bc = field.mul(&self.den, &other.num);
        let bd = field.mul(&self.den, &other.den);
        Fraction::new(field.sub(&ad, &bc), bd)
    }

    pub fn to_field_element(&self, field: &F) -> Option<T> {
        let nz = field.get_non_zero(&self.den)?;
        Some(field.div(&self.num, &nz))
    }
}

impl Group<bool> for bool {
    fn additive_identity(&self) -> bool {
        false
    }

    fn add(&self, x: &bool, y: &bool) -> bool {
        x ^ y
    }

    fn eq_group(&self, _: &Self) -> bool {
        true
    }

    fn additive_inverse(&self, x: &bool) -> bool {
        *x
    }

    fn sub(&self, x: &bool, y: &bool) -> bool {
        x ^ y
    }

    fn clone(&self, x: &bool) -> bool {
        *x
    }

    fn eq(&self, x: &bool, y: &bool) -> bool {
        x == y
    }

    fn is_additive_identity(&self, x: &bool) -> bool {
        !x
    }

    fn repeated_addition(&self, x: bool, n: &Integer) -> bool {
        if x { n.get_bit(0) } else { false }
    }

    fn group_exponent(&self) -> Option<Integer> {
        // 2 * false = false
        // 2 * true = false
        Some(2.into())
    }
}

impl Ring<bool> for bool {
    fn mul(&self, x: &bool, y: &bool) -> bool {
        x & y
    }

    fn eq_ring(&self, _: &Self) -> bool {
        true
    }

    fn multiplicative_identity(&self) -> bool {
        true
    }

    fn ring_exponent(&self) -> Option<Integer> {
        // true^1 = 1
        Some(1.into())
    }
}

impl CompleteRing<bool> for bool {
    fn multiplicative_inverse(&self, x: &bool) -> Option<bool> {
        if *x { Some(true) } else { None }
    }
}

// Because bool is isomorphic to Z/2Z, which is a field because 2 is prime
impl Field<bool, ()> for bool {
    fn eq_field(&self, _: &Self) -> bool {
        true
    }

    fn characteristic(&self) -> Integer {
        // characteristic of Z/p^nZ is p
        2.into()
    }

    fn div(&self, x: &bool, _: &()) -> bool {
        // non zero bool is 1, divide by 1 is identity
        *x
    }

    fn construct_non_zero(&self, x: bool) -> Option<()> {
        if x { Some(()) } else { None }
    }

    fn deconstruct_non_zero(&self, _: ()) -> bool {
        true
    }

    fn get_non_zero(&self, x: &bool) -> Option<()> {
        if *x { Some(()) } else { None }
    }

    fn get_element_from_non_zero(&self, _: &()) -> bool {
        true
    }
}

impl FiniteField<bool, (), usize> for bool {
    fn order(&self) -> usize {
        2
    }
}

macro_rules! mod2n_inv {
    ($x:expr, $n:expr, $T:ty) => {{
        let x: $T = $x;
        let n: u32 = $n;

        if x % 2 == 0 {
            None
        } else {
            let mut y: $T = 1;
            let mut m: $T = 2;

            while m < (1 << n) {
                y = y.wrapping_mul((2 as$T).wrapping_sub(x.wrapping_mul(y))) % (m << 1);
                m <<= 1;
            }

            Some(y & ((1 as $T).wrapping_shl(n) - 1))
        }
    }};
}

macro_rules! group_impl_native_type {
    ($t: ident) => {
        impl Group<$t> for $t {
            fn additive_identity(&self) -> $t {
                0
            }

            fn add(&self, x: &$t, y: &$t) -> $t {
                x.wrapping_add(*y)
            }

            fn eq_group(&self, _: &$t) -> bool {
                true
            }

            fn additive_inverse(&self, x: &$t) -> $t {
                x.wrapping_neg()
            }

            fn sub(&self, x: &$t, y: &$t) -> $t {
                x.wrapping_sub(*y)
            }

            fn clone(&self, x: &$t) -> $t {
                *x
            }

            fn eq(&self, x: &$t, y: &$t) -> bool {
                x == y
            }

            fn is_additive_identity(&self, x: &$t) -> bool {
                *x == 0
            }

            fn group_exponent(&self) -> Option<Integer> {
                // Show that 1 doesn't work: 1 * 2 = 2 != 1
                // Show that n < this_group_size doesn't work: n * 1 = n != 1
                // Now show that n=this_group_size works: Let k be an element of the group, then nk mod this_group_size = nk mod n = 0. Works.
                Some(Integer::from($t::MAX) + 1)
            }
        }
    };
}

macro_rules! ring_impl_native_type {
    ($t: ident, $numbits: expr) => {
        impl Ring<$t> for $t {
            fn eq_ring(&self, _: &$t) -> bool {
                true
            }

            fn mul(&self, x: &$t, y: &$t) -> $t {
                x.wrapping_mul(*y)
            }

            fn multiplicative_identity(&self) -> $t {
                1
            }

            fn ring_exponent(&self) -> Option<Integer> {
                // 2^k mod 2^n is never 1 for non zero k !
                None
            }
        }

        impl CompleteRing<$t> for $t {
            fn multiplicative_inverse(&self, x: &$t) -> Option<$t> {
                mod2n_inv!(*x, $numbits, $t)
            }
        }
    };
}

pub trait EuclideanDivisible<UselessData = ()>: Sized + Debug {
    /// Returns (quotient, remainder) such that self = divisor * quotient + remainder, or None if self is not divisible by divisor
    fn euclidean_division(&self, other: &Self) -> Option<(Self, Self)>;

    /// Returns true if `self` is the additive identity (i.e. "zero").
    fn is_zero(&self) -> bool;

    /// Clones `self`.
    fn clone(&self) -> Self;

    /// Compute the greatest common divisor using the Euclidean algorithm.
    fn gcd(&self, other: &Self) -> Self {
        let mut me = self.clone();
        let mut other = other.clone();
        while !other.is_zero() {
            let Some((_, r)) = self.euclidean_division(&other) else {
                // other was zero and it fucking lied :(
                break;
            };
            me = other;
            other = r;
        }
        me
    }
}

group_impl_native_type!(i8);
group_impl_native_type!(u8);
group_impl_native_type!(i16);
group_impl_native_type!(u16);
group_impl_native_type!(i32);
group_impl_native_type!(u32);
group_impl_native_type!(i64);
group_impl_native_type!(u64);
group_impl_native_type!(i128);
group_impl_native_type!(u128);
group_impl_native_type!(isize);
group_impl_native_type!(usize);

ring_impl_native_type!(u8, 8);
ring_impl_native_type!(u16, 16);
ring_impl_native_type!(u32, 32);
ring_impl_native_type!(u64, 64);
ring_impl_native_type!(u128, 128);

#[cfg(test)]
mod tests {
    use crate::algebra::{Group, Ring};

    #[test]
    fn test_repeated_addition() {
        for m in 0..1000 {
            for n in 0..1000 {
                assert_eq!(0.repeated_addition(m, &n.into()), m * n);
            }
        }
    }

    #[test]
    fn test_ring_pow() {
        for m in 0..1000 {
            for n in 0..1000 {
                assert_eq!(Ring::power(&0u64, &m, &n.into()), Some(m.wrapping_pow(n)));
            }
        }
    }
}
