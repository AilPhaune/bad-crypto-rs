use std::fmt::Debug;

use rug::{Complete, Integer, integer::IsPrime, ops::RemRounding};

use crate::{
    Checked, Unchecked,
    algebra::{CheckIsPrime, CompleteRing, Field, FiniteField, Group, Ring},
};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrimeField {
    modulus: Integer,
}

impl PrimeField {
    /// # Safety
    /// If modulus is not prime, Z/nZ will not be a field
    pub unsafe fn new_unchecked(modulus: Integer) -> Unchecked<PrimeField> {
        Unchecked::new(PrimeField { modulus })
    }

    pub fn new(modulus: Integer) -> Option<Checked<PrimeField>> {
        match modulus.is_prime() {
            IsPrime::No => None,
            IsPrime::Probably => Some(Checked::Unchecked(Unchecked::new(PrimeField { modulus }))),
            IsPrime::Yes => Some(Checked::Checked(PrimeField { modulus })),
        }
    }

    pub fn modulus(&self) -> &Integer {
        &self.modulus
    }

    pub fn norm(&self, z: &Integer) -> Integer {
        z.rem_euc(&self.modulus).complete()
    }

    pub fn multiplicative_group(self) -> CyclicPrimeMultiplicativeGroup {
        CyclicPrimeMultiplicativeGroup {
            modulus: self.modulus,
        }
    }

    pub fn temp_multiplicative_group<'a>(&'a self) -> TempCyclicPrimeMultiplicativeGroup<'a> {
        TempCyclicPrimeMultiplicativeGroup {
            modulus: &self.modulus,
        }
    }
}

impl Group<Integer> for PrimeField {
    fn group_exponent(&self) -> Option<Integer> {
        Some(self.modulus.clone())
    }

    fn eq_group(&self, other: &Self) -> bool {
        self.modulus == other.modulus
    }

    fn additive_identity(&self) -> Integer {
        0.into()
    }

    fn is_additive_identity(&self, x: &Integer) -> bool {
        self.norm(x) == 0
    }

    fn additive_inverse(&self, x: &Integer) -> Integer {
        self.norm(&x.as_neg())
    }

    fn add(&self, x: &Integer, y: &Integer) -> Integer {
        let z = (x + y).complete();
        self.norm(&z)
    }

    fn clone(&self, x: &Integer) -> Integer {
        self.norm(x)
    }

    fn sub(&self, x: &Integer, y: &Integer) -> Integer {
        let z = (x - y).complete();
        self.norm(&z)
    }

    fn eq(&self, x: &Integer, y: &Integer) -> bool {
        self.norm(x) == self.norm(y)
    }

    fn repeated_addition(&self, x: Integer, n: &Integer) -> Integer {
        self.norm(&(x * n))
    }
}

impl Ring<Integer> for PrimeField {
    fn eq_ring(&self, other: &Self) -> bool {
        self.modulus == other.modulus
    }

    fn multiplicative_identity(&self) -> Integer {
        1.into()
    }

    fn mul(&self, x: &Integer, y: &Integer) -> Integer {
        let z = (x * y).complete();
        self.norm(&z)
    }

    fn ring_exponent(&self) -> Option<Integer> {
        // By fermat's little theorem, for non-zero x, x^(p-1) = 1
        Some((&self.modulus - Integer::ONE).complete())
    }
}

impl CompleteRing<Integer> for PrimeField {
    fn multiplicative_inverse(&self, x: &Integer) -> Option<Integer> {
        x.clone().invert(&self.modulus).ok()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PrimeFieldNonZeroInteger(Integer);

impl PrimeFieldNonZeroInteger {
    pub fn get_ref(&self) -> &Integer {
        &self.0
    }

    pub fn get(self) -> Integer {
        self.0
    }
}

impl Field<Integer, PrimeFieldNonZeroInteger> for PrimeField {
    fn eq_field(&self, other: &Self) -> bool {
        self.modulus == other.modulus
    }

    fn characteristic(&self) -> Integer {
        self.modulus.clone()
    }

    fn construct_non_zero(&self, x: Integer) -> Option<PrimeFieldNonZeroInteger> {
        let x = self.norm(&x);
        if x.is_zero() {
            None
        } else {
            Some(PrimeFieldNonZeroInteger(x))
        }
    }

    fn deconstruct_non_zero(&self, x: PrimeFieldNonZeroInteger) -> Integer {
        x.0
    }

    fn get_element_from_non_zero(&self, x: &PrimeFieldNonZeroInteger) -> Integer {
        x.0.clone()
    }

    fn get_non_zero(&self, x: &Integer) -> Option<PrimeFieldNonZeroInteger> {
        let x = self.norm(x);
        if x.is_zero() {
            None
        } else {
            Some(PrimeFieldNonZeroInteger(x))
        }
    }

    fn div(&self, x: &Integer, y: &PrimeFieldNonZeroInteger) -> Integer {
        self.mul(x, &self.multiplicative_inverse(&y.0).unwrap())
    }
}

impl FiniteField<Integer, PrimeFieldNonZeroInteger, Integer> for PrimeField {
    fn order(&self) -> Integer {
        self.modulus.clone()
    }
}

#[derive(Debug)]
pub struct CyclicPrimeMultiplicativeGroup {
    modulus: Integer,
}

#[derive(Debug)]
pub struct TempCyclicPrimeMultiplicativeGroup<'a> {
    modulus: &'a Integer,
}

impl CyclicPrimeMultiplicativeGroup {
    /// # Safety
    /// If modulus is not prime, Z/nZ will not have a multiplicative group
    pub unsafe fn new_unchecked(modulus: Integer) -> Unchecked<CyclicPrimeMultiplicativeGroup> {
        Unchecked::new(CyclicPrimeMultiplicativeGroup { modulus })
    }

    pub fn new(modulus: Integer) -> Option<Checked<CyclicPrimeMultiplicativeGroup>> {
        match modulus.is_prime() {
            IsPrime::No => None,
            IsPrime::Probably => Some(Checked::Unchecked(Unchecked::new(
                CyclicPrimeMultiplicativeGroup { modulus },
            ))),
            IsPrime::Yes => Some(Checked::Checked(CyclicPrimeMultiplicativeGroup { modulus })),
        }
    }

    pub fn modulus(&self) -> &Integer {
        &self.modulus
    }

    pub fn norm(&self, z: &Integer) -> Integer {
        z.rem_euc(&self.modulus).complete()
    }
}

impl<'a> TempCyclicPrimeMultiplicativeGroup<'a> {
    pub fn modulus(&self) -> &Integer {
        self.modulus
    }

    pub fn norm(&self, z: &Integer) -> Integer {
        z.rem_euc(self.modulus).complete()
    }
}

// The group is (Z/pZ \ {0}, *)
impl Group<Integer> for CyclicPrimeMultiplicativeGroup {
    fn group_exponent(&self) -> Option<Integer> {
        Some((&self.modulus - Integer::ONE).complete())
    }

    fn eq_group(&self, other: &Self) -> bool {
        self.modulus == other.modulus
    }

    fn additive_identity(&self) -> Integer {
        1.into()
    }

    fn add(&self, x: &Integer, y: &Integer) -> Integer {
        let z = (x * y).complete();
        self.norm(&z)
    }

    fn additive_inverse(&self, x: &Integer) -> Integer {
        x.clone().invert(&self.modulus).unwrap()
    }

    fn clone(&self, x: &Integer) -> Integer {
        self.norm(x)
    }

    fn eq(&self, x: &Integer, y: &Integer) -> bool {
        self.norm(x) == self.norm(y)
    }

    fn is_additive_identity(&self, x: &Integer) -> bool {
        self.norm(x) == 1
    }
}

// The group is (Z/pZ \ {0}, *)
impl<'a> Group<Integer> for TempCyclicPrimeMultiplicativeGroup<'a> {
    fn group_exponent(&self) -> Option<Integer> {
        Some((self.modulus - Integer::ONE).complete())
    }

    fn eq_group(&self, other: &Self) -> bool {
        self.modulus == other.modulus
    }

    fn additive_identity(&self) -> Integer {
        1.into()
    }

    fn add(&self, x: &Integer, y: &Integer) -> Integer {
        let z = (x * y).complete();
        self.norm(&z)
    }

    fn additive_inverse(&self, x: &Integer) -> Integer {
        x.clone().invert(self.modulus).unwrap()
    }

    fn clone(&self, x: &Integer) -> Integer {
        self.norm(x)
    }

    fn eq(&self, x: &Integer, y: &Integer) -> bool {
        self.norm(x) == self.norm(y)
    }

    fn is_additive_identity(&self, x: &Integer) -> bool {
        self.norm(x) == 1
    }
}
