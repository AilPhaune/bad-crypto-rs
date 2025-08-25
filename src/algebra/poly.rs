use std::fmt::Debug;

use rug::Integer;

use crate::algebra::{EuclideanDivisible, Field, Group, Ring};

#[derive(Debug)]
pub struct Polynomial<'a, T: Debug, R: Ring<T>> {
    ring: &'a R,
    // coeffs[idx] is the coefficient of x^idx
    coeffs: Vec<T>,
}

impl<'a, T: Debug, R: Ring<T>> Polynomial<'a, T, R> {
    pub fn new(field: &'a R, mut coeffs: Vec<T>) -> Self {
        while let Some(c) = coeffs.last() {
            if field.is_additive_identity(c) {
                coeffs.pop();
            } else {
                break;
            }
        }

        Self {
            ring: field,
            coeffs,
        }
    }

    pub fn degree(&self) -> i64 {
        self.coeffs.len() as i64 - 1
    }

    pub fn eval(&self, x: &T) -> T {
        let mut res = self.ring.additive_identity();
        for coeff in self.coeffs.iter().rev() {
            res = self.ring.mul(&res, x);
            res = self.ring.add(&res, coeff);
        }
        res
    }

    /// Returns self + other as a new polynomial, it supposes that other.field == self.field
    pub fn add(&self, other: &Self) -> Self {
        let res_len = self.coeffs.len().max(other.coeffs.len());
        let mut coeffs = Vec::with_capacity(res_len);
        for i in 0..res_len {
            match (self.coeffs.get(i), other.coeffs.get(i)) {
                (Some(c1), Some(c2)) => coeffs.push(self.ring.add(c1, c2)),
                (Some(c1), None) => coeffs.push(self.ring.clone(c1)),
                (None, Some(c2)) => coeffs.push(self.ring.clone(c2)),
                (None, None) => break,
            }
        }
        Polynomial::new(self.ring, coeffs)
    }

    /// Returns self - other as a new polynomial, it supposes that other.field == self.field
    pub fn sub(&self, other: &Self) -> Self {
        let res_len = self.coeffs.len().max(other.coeffs.len());
        let mut coeffs = Vec::with_capacity(res_len);
        for i in 0..res_len {
            match (self.coeffs.get(i), other.coeffs.get(i)) {
                (Some(c1), Some(c2)) => coeffs.push(self.ring.sub(c1, c2)),
                (Some(c1), None) => coeffs.push(self.ring.clone(c1)),
                (None, Some(c2)) => coeffs.push(self.ring.additive_inverse(c2)),
                (None, None) => break,
            }
        }
        Polynomial::new(self.ring, coeffs)
    }

    /// Returns -self
    pub fn neg(&self) -> Self {
        Self::new(
            self.ring,
            self.coeffs
                .iter()
                .map(|coeff| self.ring.additive_inverse(coeff))
                .collect(),
        )
    }

    /// Returns self * other as a new polynomial, it supposes that other.field == self.field
    pub fn mul(&self, other: &Self) -> Self {
        let res_len = self.coeffs.len() + other.coeffs.len() - 1;
        let mut coeffs = Vec::with_capacity(res_len);
        for i in 0..res_len {
            let mut sum = self.ring.additive_identity();
            for a in 0..=i {
                let b = i - a;
                match (self.coeffs.get(a), other.coeffs.get(b)) {
                    (Some(c1), Some(c2)) => sum = self.ring.add(&sum, &self.ring.mul(c1, c2)),
                    (None, _) => break, // a gets bigger, so if it went pas self.coeffs's end then there won't be any more coeffs to add
                    (_, _) => continue,
                }
            }
            coeffs.push(sum);
        }
        Polynomial::new(self.ring, coeffs)
    }

    pub fn pow(&self, exp: u32) -> Self {
        // Double-and-add

        // P(x) = 1
        let mut res = Polynomial::new(self.ring, vec![self.ring.multiplicative_identity()]);

        let bits = u32::BITS - exp.leading_zeros();

        for i in (0..bits).rev() {
            res = res.mul(&res);
            if exp & (1 << i) != 0 {
                res = res.mul(self);
            }
        }

        res
    }

    pub fn get_ring(&self) -> &'a R {
        self.ring
    }

    pub fn get_coefficients(&self) -> &[T] {
        &self.coeffs
    }
}

impl<'a, T: Debug, R: Ring<T>> PartialEq for Polynomial<'a, T, R> {
    fn eq(&self, other: &Self) -> bool {
        self.ring.eq_ring(other.ring)
            && self.coeffs.len() == other.coeffs.len()
            && self
                .coeffs
                .iter()
                .zip(other.coeffs.iter())
                .all(|(c1, c2)| self.ring.eq(c1, c2))
    }
}

impl<'a, T: Debug, R: Ring<T>> Eq for Polynomial<'a, T, R> {}

#[derive(Debug)]
pub struct PolynomialRing<'a, T: Debug, R: Ring<T>> {
    ring: &'a R,
    zero: Polynomial<'a, T, R>,
    one: Polynomial<'a, T, R>,
}

impl<'a, T: Debug, R: Ring<T>> PolynomialRing<'a, T, R> {
    pub fn new_from_poly(poly: &Polynomial<'a, T, R>) -> Self {
        Self {
            ring: &poly.ring,
            zero: Polynomial::new(poly.ring, vec![]),
            one: Polynomial::new(poly.ring, vec![poly.ring.multiplicative_identity()]),
        }
    }

    pub fn new(ring: &'a R) -> Self {
        Self {
            ring,
            zero: Polynomial::new(ring, vec![]),
            one: Polynomial::new(ring, vec![ring.multiplicative_identity()]),
        }
    }
}

impl<'a, T: Debug, R: Ring<T>> Group<Polynomial<'a, T, R>> for PolynomialRing<'a, T, R> {
    fn group_exponent(&self) -> Option<Integer> {
        // let N be the group exponent of the ring on which the polynomial is defined
        // Then n < N can't be the group exponent of the polynomial ring, because [n] * 1 ( [the polynomial 1] added n times) is equal to
        // the polynomial ([1] added n times), which by definition of N is not the zero polynomial.
        // Then n = N works, because consider any polynomial P of coefficients a_0, a_1, ..., a_k. Then [n] * P = is the polynomial of
        // coefficients N a_0, N a_1, ..., N a_k, which by definition of N makes all coefficients equal to zero.
        self.ring.group_exponent()
    }

    fn add(&self, x: &Polynomial<'a, T, R>, y: &Polynomial<'a, T, R>) -> Polynomial<'a, T, R> {
        x.add(y)
    }

    fn additive_identity(&self) -> Polynomial<'a, T, R> {
        self.clone(&self.zero)
    }

    fn additive_inverse(&self, x: &Polynomial<'a, T, R>) -> Polynomial<'a, T, R> {
        x.neg()
    }

    fn clone(&self, x: &Polynomial<'a, T, R>) -> Polynomial<'a, T, R> {
        Polynomial::new(
            self.ring,
            x.coeffs.iter().map(|c| self.ring.clone(c)).collect(),
        )
    }

    fn eq(&self, x: &Polynomial<'a, T, R>, y: &Polynomial<'a, T, R>) -> bool {
        x == y
    }

    fn eq_group(&self, other: &Self) -> bool {
        self.ring.eq_ring(other.ring)
    }

    fn is_additive_identity(&self, x: &Polynomial<'a, T, R>) -> bool {
        x == &self.zero
    }
}

impl<'a, T: Debug, R: Ring<T>> Ring<Polynomial<'a, T, R>> for PolynomialRing<'a, T, R> {
    fn ring_exponent(&self) -> Option<Integer> {
        // Suppose for contradiction that there exists an integer n such that for all polynomials P, P^n = 1.
        // Then let Q be the polynomial x + 1. This implies Q^n = 1, therefore 1 = Q(-1) = ((-1) + 1)^n = 0^n = 0 is a contradiction.
        None
    }

    fn mul(&self, x: &Polynomial<'a, T, R>, y: &Polynomial<'a, T, R>) -> Polynomial<'a, T, R> {
        x.mul(y)
    }

    fn eq_ring(&self, other: &Self) -> bool {
        self.ring.eq_ring(other.ring)
    }

    fn multiplicative_identity(&self) -> Polynomial<'a, T, R> {
        self.clone(&self.one)
    }
}

impl<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> EuclideanDivisible<NZ> for Polynomial<'a, T, F> {
    fn euclidean_division(
        &self,
        divisor: &Polynomial<T, F>,
    ) -> Option<(Polynomial<'a, T, F>, Polynomial<'a, T, F>)> {
        // it's a field
        let field = self.ring;

        let mut remainder: Vec<T> = self.coeffs.iter().map(|c| field.clone(c)).collect();
        let mut quotient: Vec<T> = remainder
            .iter()
            .map(|_| field.additive_identity())
            .collect();

        let deg_divisor = divisor.coeffs.len() - 1;
        let lc_divisor = field.get_non_zero(&divisor.coeffs[deg_divisor])?; // leading coefficient

        while remainder.len() >= divisor.coeffs.len() {
            let deg_rem = remainder.len() - 1;
            let lc_rem = field.clone(&remainder[deg_rem]);

            // coeff = lc_rem / lc_divisor
            let coeff = field.div(&lc_rem, &lc_divisor);
            let deg_diff = deg_rem - deg_divisor;
            quotient[deg_diff] = field.clone(&coeff);

            // subtract coeff * x^deg_diff * divisor from remainder
            for i in 0..=deg_divisor {
                let idx = i + deg_diff;
                let subtrahend = field.mul(&divisor.coeffs[i], &coeff);
                remainder[idx] = field.sub(&remainder[idx], &subtrahend);
            }

            // remove trailing zeros
            while remainder
                .last()
                .map_or(false, |x| field.is_additive_identity(x))
            {
                remainder.pop();
            }
        }

        // shrink quotient to proper size
        quotient.truncate(self.coeffs.len() - divisor.coeffs.len() + 1);

        Some((
            Polynomial::new(self.ring, quotient),
            Polynomial::new(self.ring, remainder),
        ))
    }

    fn clone(&self) -> Self {
        Polynomial::new(
            self.ring,
            self.coeffs.iter().map(|c| self.ring.clone(c)).collect(),
        )
    }

    fn is_zero(&self) -> bool {
        self.coeffs.len() == 0
    }
}

#[cfg(test)]
mod tests {
    use rug::Integer;

    use super::*;
    use crate::algebra::modular::PrimeField;

    #[test]
    fn test_poly_eval() {
        let field = PrimeField::new(59.into()).unwrap().get_checked().unwrap();

        // 2 + 17x + 13x^2 + 20x^3 + 4x^4
        let coeffs = [2, 17, 13, 20, 4]
            .iter()
            .map(|c| Integer::from(*c))
            .collect();

        let poly = Polynomial::new(&field, coeffs);

        for x in 0..59 {
            assert_eq!(
                poly.eval(&Integer::from(x)),
                field.norm(&Integer::from(
                    2 + 17 * x + 13 * x * x + 20 * x * x * x + 4 * x * x * x * x
                ))
            );
        }
    }

    #[test]
    fn test_poly_mul() {
        let field = PrimeField::new(59.into()).unwrap().get_checked().unwrap();

        // 2 + 17x + 13x^2 + 20x^3 + 4x^4
        let coeffs1 = [2, 17, 13, 20, 4]
            .iter()
            .map(|c| Integer::from(*c))
            .collect();

        let poly1 = Polynomial::new(&field, coeffs1);

        // 3 + 5x + 2x^2 + 4x^3
        let coeffs2 = [3, 5, 2, 4].iter().map(|c| Integer::from(*c)).collect();

        let poly2 = Polynomial::new(&field, coeffs2);

        // (2 + 17x + 13x^2 + 20x^3 + 4x^4) (3 + 5x + 2x^2 + 4x^3)
        // =   2*3 + 17*3 x + 13*3 x^2 + 20*3 x^3 + 4*3  x^4
        //   +       2*5  x + 17*5 x^2 + 13*5 x^3 + 20*5 x^4 + 4*5  x^5
        //   +                2*2  x^2 + 17*2 x^3 + 13*2 x^4 + 20*2 x^5 + 4*2 x^6
        //   +                           2*4  x^3 + 17*4 x^4 + 13*4 x^5 + 20*4 x^6 + 4*4 x^7
        // =   6   + 61   x + 128  x^2 + 167  x^3 + 206  x^4 + 112  x^5 + 88   x^6 + 16  x^7
        // = 6 + 2x + 10x^2 + 49x^3 + 29x^4 + 53x^5 + 29x^6 + 16x^7

        let coeffs3: Vec<_> = [6, 2, 10, 49, 29, 53, 29, 16]
            .iter()
            .map(|c| Integer::from(*c))
            .collect();

        let res = poly1.mul(&poly2);

        assert_eq!(res.coeffs, coeffs3);
    }

    #[test]
    fn test_pow() {
        let field = PrimeField::new(59.into()).unwrap().get_checked().unwrap();

        // 2 + 17x + 13x^2 + 20x^3 + 4x^4
        let coeffs = [2, 17, 13, 20, 4]
            .iter()
            .map(|c| Integer::from(*c))
            .collect();

        let poly = Polynomial::new(&field, coeffs);
        let ring = PolynomialRing::new_from_poly(&poly);

        let mut pow_n = ring.clone(&poly);

        for n in 2..100 {
            pow_n = pow_n.mul(&poly);
            let repeated_squared = poly.pow(n);

            assert_eq!(pow_n, repeated_squared);
        }
    }

    #[test]
    fn test_euclidean_division() {
        let field = PrimeField::new(59.into()).unwrap().get_checked().unwrap();

        // 2 + 17x + 13x^2 + 20x^3 + 4x^4
        let coeffs = [2, 17, 13, 20, 4]
            .iter()
            .map(|c| Integer::from(*c))
            .collect();

        let poly = Polynomial::new(&field, coeffs);

        // 3 + 5x + 2x^2 + 4x^3
        let coeffs2 = [3, 5, 2, 4].iter().map(|c| Integer::from(*c)).collect();

        let poly2 = Polynomial::new(&field, coeffs2);

        let (quotient, remainder) = poly.euclidean_division(&poly2).unwrap();

        // multiply back
        let res = quotient.mul(&poly2).add(&remainder);
        assert_eq!(res, poly);
        assert!(remainder.degree() < poly2.degree());
    }
}
