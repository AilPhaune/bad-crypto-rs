use std::{fmt::Debug, marker::PhantomData};

use rug::Integer;

use crate::algebra::{CyclicGroup, Group};

pub struct ElGamalKeygen<'a, T: Debug, G: ElGamalCapable<T>> {
    group: &'a G,
    generator: &'a T,
}

impl<'a, T: Debug, G: ElGamalCapable<T>> ElGamalKeygen<'a, T, G> {
    pub fn new(group: &'a G, generator: &'a T) -> Self {
        Self { group, generator }
    }

    pub fn generate_keypair(
        &self,
        private_key: Integer,
    ) -> (ElGamalPrivateKey<'a, T, G>, ElGamalPublicKey<'a, T, G>) {
        let public_key = ElGamalPublicKey {
            group: self.group,
            generator: self.generator,
            h: self
                .group
                .pow(self.group.clone(self.generator), &private_key),
        };
        let private_key = ElGamalPrivateKey {
            _phantom: PhantomData,
            group: self.group,
            sk: private_key,
        };
        (private_key, public_key)
    }
}

pub struct ElGamalPublicKey<'a, T: Debug, G: ElGamalCapable<T>> {
    group: &'a G,
    generator: &'a T,
    h: T,
}

impl<'a, T: Debug, G: ElGamalCapable<T>> ElGamalPublicKey<'a, T, G> {
    pub fn encrypt(&self, m: T, r: &Integer) -> (T, T) {
        let t = self.group.pow(self.group.clone(&self.h), r);
        let c2 = self.group.mul(&m, &t);
        let c1 = self.group.pow(self.group.clone(self.generator), r);
        (c1, c2)
    }
}

pub struct ElGamalPrivateKey<'a, T: Debug, G: ElGamalCapable<T>> {
    _phantom: PhantomData<T>,
    group: &'a G,
    sk: Integer,
}

impl<'a, T: Debug, G: ElGamalCapable<T>> ElGamalPrivateKey<'a, T, G> {
    pub fn decrypt(&self, cipher: (&T, &T)) -> T {
        let s = self
            .group
            .pow(self.group.clone(cipher.0), &self.sk.as_neg());
        self.group.mul(cipher.1, &s)
    }
}

pub trait ElGamalCapable<T: Debug>: Debug {
    fn group_order(&self) -> Integer;
    fn pow(&self, base: T, exponent: &Integer) -> T;
    fn mul(&self, x: &T, y: &T) -> T;
    fn clone(&self, x: &T) -> T;
}

impl<T: Debug, G: CyclicGroup<T>> ElGamalCapable<T> for G {
    fn group_order(&self) -> Integer {
        CyclicGroup::order(self)
    }

    fn pow(&self, base: T, exponent: &Integer) -> T {
        self.repeated_addition(base, exponent)
    }

    fn mul(&self, x: &T, y: &T) -> T {
        self.add(x, y)
    }

    fn clone(&self, x: &T) -> T {
        Group::clone(self, x)
    }
}

#[cfg(test)]
mod tests {
    use rug::Integer;

    use crate::{
        algebra::modular::PrimeField,
        algorithms::el_gamal::ElGamalKeygen,
        math::randomness::{
            CryptographicallySecureRandomIntegerGenerator, TestRandomIntegerGenerator,
        },
    };

    #[test]
    fn test_el_gamal_mod_2147483647() {
        let prime = 2147483647.into();
        let field = PrimeField::new(prime)
            .unwrap()
            .get_checked()
            .unwrap()
            .multiplicative_group();
        let generator = 2.into();

        let keygen = ElGamalKeygen::new(&field, &generator);
        let (private_key, public_key) = keygen.generate_keypair(12345.into());

        let message: Integer = 314159265.into();
        let r = 98765.into();
        let cipher = public_key.encrypt(message.clone(), &r);
        let decrypted_message = private_key.decrypt((&cipher.0, &cipher.1));
        assert_eq!(message, decrypted_message);
    }

    #[test]
    fn test_el_gamal_mod_2147483647_with_rng() {
        let prime = 2147483647.into();
        let field = PrimeField::new(prime)
            .unwrap()
            .get_checked()
            .unwrap()
            .multiplicative_group();
        let generator = 2.into();

        let mut rng = TestRandomIntegerGenerator::default();

        for i in 0..100 {
            let keygen = ElGamalKeygen::new(&field, &generator);
            let mut pvk_bytes = [0u8; 4];
            rng.get_bytes(&mut pvk_bytes);
            let pvk = Integer::from(u32::from_le_bytes(pvk_bytes));
            let (private_key, public_key) = keygen.generate_keypair(pvk);

            let message: Integer = 314159265.into();
            let mut r_bytes = [0u8; 4];
            rng.get_bytes(&mut r_bytes);
            let r = Integer::from(u32::from_le_bytes(r_bytes));
            let cipher = public_key.encrypt(message.clone(), &r);

            let decrypted_message = private_key.decrypt((&cipher.0, &cipher.1));
            assert_eq!(message, decrypted_message, "failed at iteration {}", i);
        }
    }
}
