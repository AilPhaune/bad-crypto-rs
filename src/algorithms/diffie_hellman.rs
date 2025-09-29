use std::{fmt::Debug, marker::PhantomData};

use rug::Integer;

use crate::algebra::Group;

#[derive(Debug)]
pub struct DiffieHellman<'a, T: Debug, G: DiffieHellmanCapable<T>> {
    _phantom: PhantomData<T>,
    dh_group: &'a G,
    private_key: Integer,
    public_key: T,
}

pub trait DiffieHellmanCapable<T: Debug>: Debug {
    fn dh(&self, a: T, b: &Integer) -> T;
}

impl<T: Debug, G: Group<T>> DiffieHellmanCapable<T> for G {
    fn dh(&self, a: T, b: &Integer) -> T {
        self.repeated_addition(a, b)
    }
}

impl<'a, T: Debug, G: DiffieHellmanCapable<T>> DiffieHellman<'a, T, G> {
    pub fn new(dh_group: &'a G, generator: T, private_key: Integer) -> Self {
        Self {
            _phantom: PhantomData,
            public_key: dh_group.dh(generator, &private_key),
            private_key,
            dh_group,
        }
    }

    pub fn get_pbk(&self) -> &T {
        &self.public_key
    }

    pub fn get_pvk(&self) -> &Integer {
        &self.private_key
    }

    pub fn get_dh_group(&self) -> &G {
        self.dh_group
    }

    pub fn compute_shared_secret(&self, other: T) -> T {
        self.dh_group.dh(other, &self.private_key)
    }
}

#[cfg(test)]
mod tests {
    use std::str::FromStr;

    use rug::{Integer, integer::Order};

    use crate::{
        algebra::{
            Group,
            modular::{CyclicPrimeMultiplicativeGroup, PrimeField},
        },
        algorithms::diffie_hellman::DiffieHellman,
        structures::curves::elliptic::{
            MontgomeryEllipticCurve, WeierstrassEllipticCurve, get_curve25519,
        },
    };

    #[test]
    pub fn test_dh_on_multiplicative_group() {
        let p: Integer = 999_999_937.into(); // largest prime < a billion

        let group = CyclicPrimeMultiplicativeGroup::new(p)
            .unwrap()
            .get_checked()
            .unwrap();

        let generator = Integer::from(2);

        let alice = DiffieHellman::new(&group, generator.clone(), Integer::from(314_159_265));
        let bob = DiffieHellman::new(&group, generator.clone(), Integer::from(271_828_182));

        let alice_pub = alice.get_pbk().clone();
        let bob_pub = bob.get_pbk().clone();

        // suppose they exchange their public keys, then calculate the shared secret

        let alice_shared = alice.compute_shared_secret(bob_pub);
        let bob_shared = bob.compute_shared_secret(alice_pub);

        println!("alice_shared: {}", alice_shared);
        println!("bob_shared: {}", bob_shared);

        assert_eq!(alice_shared, bob_shared);
    }

    #[test]
    pub fn test_dh_on_weierstrass_elliptic_curve() {
        let p: Integer = 999_999_937.into(); // largest prime < a billion

        // why not, they give large factors of the curve order
        let a: Integer = 2.into();
        let b: Integer = 6.into();

        let field = PrimeField::new(p).unwrap().get_checked().unwrap();
        let curve = WeierstrassEllipticCurve::create_curve(&field, a, b).unwrap();
        let generator = curve.get_point_at(1.into(), 3.into()).unwrap();

        /*{
            let mut i = 1;
            let mut p = curve.clone(&generator);

            while !curve.is_additive_identity(&p) {
                i += 1;
                p = curve.add(&p, &generator);
            }

            println!("GENERATOR GENERATES {} POINTS", i); // 166_665_404
        }*/

        // DH
        let alice = DiffieHellman::new(&curve, curve.clone(&generator), Integer::from(314_159_265));
        let bob = DiffieHellman::new(&curve, curve.clone(&generator), Integer::from(271_828_182));

        let alice_pub = curve.clone(alice.get_pbk());
        let bob_pub = curve.clone(bob.get_pbk());

        // suppose they exchange their public keys, then calculate the shared secret

        let alice_shared = alice.compute_shared_secret(bob_pub);
        let bob_shared = bob.compute_shared_secret(alice_pub);

        println!("alice_shared: {:?}", alice_shared);
        println!("bob_shared: {:?}", bob_shared);

        assert!(curve.eq(&alice_shared, &bob_shared));
    }

    #[test]
    pub fn test_dh_on_montgomery_elliptic_curve_with_full_point_data() {
        let p: Integer = 999_999_937.into(); // largest prime < a billion

        let field = PrimeField::new(p).unwrap().get_checked().unwrap();
        // y^2 = x^3 + 3 x^2 + x
        let curve =
            MontgomeryEllipticCurve::create_curve(&field, Integer::from(3), Integer::from(1))
                .unwrap();

        let generator = curve.get_point_at(5.into(), 252450201.into()).unwrap();

        // DH
        let alice = DiffieHellman::new(&curve, curve.clone(&generator), Integer::from(314_159_265));
        let bob = DiffieHellman::new(&curve, curve.clone(&generator), Integer::from(271_828_182));

        let alice_pub = curve.clone(alice.get_pbk());
        let bob_pub = curve.clone(bob.get_pbk());

        // suppose they exchange their public keys, then calculate the shared secret

        let alice_shared = alice.compute_shared_secret(bob_pub);
        let bob_shared = bob.compute_shared_secret(alice_pub);

        println!("alice_shared: {:?}", alice_shared);
        println!("bob_shared: {:?}", bob_shared);

        let alice_shared_reduced = curve.to_xy(&alice_shared);
        let bob_shared_reduced = curve.to_xy(&bob_shared);

        println!("alice_shared_reduced: {:?}", alice_shared_reduced);
        println!("bob_shared_reduced: {:?}", bob_shared_reduced);

        assert!(curve.eq(&alice_shared, &bob_shared));
    }

    #[test]
    pub fn test_dh_on_montgomery_elliptic_curve_with_reduced_point_data() {
        let p: Integer = 999_999_937.into(); // largest prime < a billion

        let field = PrimeField::new(p.clone()).unwrap().get_checked().unwrap();
        // y^2 = x^3 + 3 x^2 + x
        let curve =
            MontgomeryEllipticCurve::create_curve(&field, Integer::from(3), Integer::from(1))
                .unwrap();

        // Curve's order is 999981248 and it's largest prime factor is 4051, and 999981248 / 4051 = 246848
        // Multiplying a point by 246848 gives either the point at infinity or a point of order 4051
        // Here using a point at x=2, we do get a point of order 4051
        let generator = curve.ladder(Integer::from(2), Integer::from(1), &Integer::from(246848));
        assert!(
            !generator.1.is_zero(),
            "generator is the point at infinity: {:?}",
            generator
        );

        // DH
        let alice = DiffieHellman::new(&curve, generator.clone(), Integer::from(3141));
        let bob = DiffieHellman::new(&curve, generator.clone(), Integer::from(2718));

        let alice_pub = alice.get_pbk().clone();
        let bob_pub = bob.get_pbk().clone();

        // suppose they exchange their public keys, then calculate the shared secret

        let alice_shared = alice.compute_shared_secret(bob_pub);
        let bob_shared = bob.compute_shared_secret(alice_pub);

        println!("alice_shared: {:?}", alice_shared);
        println!("bob_shared: {:?}", bob_shared);

        let alice_shared_reduced = curve.to_x(&alice_shared.0, &alice_shared.1);
        let bob_shared_reduced = curve.to_x(&bob_shared.0, &bob_shared.1);

        println!("alice_shared_reduced: {:?}", alice_shared_reduced);
        println!("bob_shared_reduced: {:?}", bob_shared_reduced);

        assert!(curve.reduced_eq(
            (&alice_shared.0, &alice_shared.1),
            (&bob_shared.0, &bob_shared.1)
        ));
    }

    #[test]
    pub fn test_dh_on_curve25519() {
        let curve = get_curve25519();

        fn clamp(x: Integer) -> Integer {
            let mut out = [0u8; 32];
            x.write_digits(&mut out, Order::LsfLe);
            out[0] &= 248;
            out[31] &= 127;
            out[31] |= 64;
            Integer::from_digits(&out, Order::LsfLe)
        }

        let alice = DiffieHellman::new(
            &curve,
            (Integer::from(9), Integer::from(1)),
            clamp(
                Integer::from_str(
                    "31415926535897932384626433832795028841971693993751058209749445923078164062862",
                )
                .unwrap(),
            ),
        );

        let bob = DiffieHellman::new(
            &curve,
            (Integer::from(9), Integer::from(1)),
            clamp(
                Integer::from_str(
                    "27182818284590452353602874713526624977572470936999595749669676277240766303535",
                )
                .unwrap(),
            ),
        );

        let alice_pub = alice.get_pbk().clone();
        let bob_pub = bob.get_pbk().clone();

        // suppose they exchange their public keys, then calculate the shared secret

        let alice_shared = alice.compute_shared_secret(bob_pub);
        let bob_shared = bob.compute_shared_secret(alice_pub);

        println!("alice_shared: {:?}", alice_shared);
        println!("bob_shared: {:?}", bob_shared);

        let alice_shared_reduced = curve.to_x(&alice_shared.0, &alice_shared.1).unwrap();
        let bob_shared_reduced = curve.to_x(&bob_shared.0, &bob_shared.1).unwrap();

        println!("alice_shared_reduced: {:?}", alice_shared_reduced);
        println!("bob_shared_reduced: {:?}", bob_shared_reduced);

        let expected_from_openssl = Integer::from_digits(
            // RAW BYTES FROM OPENSSL
            &b"6ba99666596bd8f507dbda59efb57a948485c41aa837050e0389615460bb5c6d"
                .chunks(2)
                .map(|chunk| u8::from_str_radix(std::str::from_utf8(chunk).unwrap(), 16).unwrap())
                .collect::<Vec<u8>>(),
            Order::LsfLe,
        );

        println!("expected_from_openssl: {}", expected_from_openssl);

        assert_eq!(alice_shared_reduced, bob_shared_reduced);
        assert_eq!(alice_shared_reduced, expected_from_openssl);
    }
}
