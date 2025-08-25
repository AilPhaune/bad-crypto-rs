use std::{fmt::Debug, marker::PhantomData};

use crate::{
    algebra::{
        EuclideanDivisible, Field, FiniteField, Group, Ring,
        poly::{Polynomial, PolynomialRing},
    },
    structures::curves::elliptic::WeierstrassEllipticCurve,
};

#[derive(Debug)]
pub struct DivisionPolynomial<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> {
    _phantom: PhantomData<NZ>,
    poly_x: Polynomial<'a, T, F>,
    ys_in_den: u32,
    index: u32,
}

impl<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> DivisionPolynomial<'a, T, NZ, F> {
    pub fn new(poly_x: Polynomial<'a, T, F>, ys_in_den: u32, index: u32) -> Self {
        Self {
            _phantom: PhantomData,
            poly_x,
            ys_in_den,
            index,
        }
    }

    pub fn eval(
        &self,
        x: &T,
        y_inv: &T,
        generator: &DivisionPolynomialGenerator<'_, T, NZ, F>,
    ) -> Option<T> {
        let p_x = self.poly_x.eval(x);
        if self.ys_in_den == 0 {
            Some(p_x)
        } else {
            let y_inv_pow = generator.field.power(y_inv, &self.ys_in_den.into())?;
            Some(generator.field.mul(&p_x, &y_inv_pow))
        }
    }

    pub fn mul(
        &self,
        other: &DivisionPolynomial<'a, T, NZ, F>,
    ) -> DivisionPolynomial<'a, T, NZ, F> {
        let poly_x = self.poly_x.mul(&other.poly_x);
        let ys_in_den = self.ys_in_den + other.ys_in_den;
        DivisionPolynomial::new(poly_x, ys_in_den, 0)
    }

    pub fn div_2y(&self, generator: &DivisionPolynomialGenerator<'_, T, NZ, F>) -> Self {
        Self::new(
            Polynomial::new(
                self.poly_x.get_ring(),
                self.poly_x
                    .get_coefficients()
                    .iter()
                    .map(|c| generator.field.mul(&generator.half, c))
                    .collect(),
            ),
            self.ys_in_den + 1,
            0,
        )
    }

    pub fn sub<'b>(
        &self,
        other: &DivisionPolynomial<'a, T, NZ, F>,
        generator: &'b DivisionPolynomialGenerator<'a, T, NZ, F>,
    ) -> Option<Self> {
        if self.ys_in_den == other.ys_in_den {
            Some(DivisionPolynomial::new(
                self.poly_x.sub(&other.poly_x),
                self.ys_in_den,
                0,
            ))
        } else if self.ys_in_den > other.ys_in_den {
            let diff = self.ys_in_den - other.ys_in_den;
            if diff % 2 == 1 {
                return None;
            }

            let half_diff = diff / 2;
            let mul_poly = generator.curve_rhs.pow(half_diff);

            Some(DivisionPolynomial::new(
                self.poly_x.sub(&other.poly_x.mul(&mul_poly)),
                self.ys_in_den,
                0,
            ))
        } else {
            let diff = other.ys_in_den - self.ys_in_den;
            if diff % 2 == 1 {
                return None;
            }

            let half_diff = diff / 2;
            let mul_poly = generator.curve_rhs.pow(half_diff);

            Some(DivisionPolynomial::new(
                self.poly_x.mul(&mul_poly).sub(&other.poly_x),
                other.ys_in_den,
                0,
            ))
        }
    }

    pub fn add<'b>(
        &self,
        other: &DivisionPolynomial<'a, T, NZ, F>,
        generator: &'b DivisionPolynomialGenerator<'a, T, NZ, F>,
    ) -> Option<Self> {
        if self.ys_in_den == other.ys_in_den {
            Some(DivisionPolynomial::new(
                self.poly_x.add(&other.poly_x),
                self.ys_in_den,
                0,
            ))
        } else if self.ys_in_den > other.ys_in_den {
            let diff = self.ys_in_den - other.ys_in_den;
            if diff % 2 == 1 {
                return None;
            }

            let half_diff = diff / 2;
            let mul_poly = generator.curve_rhs.pow(half_diff);

            Some(DivisionPolynomial::new(
                self.poly_x.add(&other.poly_x.mul(&mul_poly)),
                self.ys_in_den,
                0,
            ))
        } else {
            let diff = other.ys_in_den - self.ys_in_den;
            if diff % 2 == 1 {
                return None;
            }

            let half_diff = diff / 2;
            let mul_poly = generator.curve_rhs.pow(half_diff);

            Some(DivisionPolynomial::new(
                self.poly_x.mul(&mul_poly).add(&other.poly_x),
                other.ys_in_den,
                0,
            ))
        }
    }

    pub fn simplify_ys(mut self, generator: &DivisionPolynomialGenerator<'a, T, NZ, F>) -> Self {
        while self.ys_in_den > 1 {
            // try to divide numerator by y^2
            if let Some((q, r)) = self.poly_x.euclidean_division(&generator.curve_rhs) {
                if generator.poly_ring.is_additive_identity(&r) {
                    self.poly_x = q;
                    self.ys_in_den -= 2;
                } else {
                    // can't divide by y^2 anymore
                    break;
                }
            }
        }

        self
    }
}

#[derive(Debug)]
pub struct DivisionPolynomialGenerator<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> {
    _phantom: PhantomData<NZ>,
    curve: &'a WeierstrassEllipticCurve<'a, T, NZ, F>,
    field: &'a F,
    half: T,
    poly_ring: PolynomialRing<'a, T, F>,
    curve_rhs: Polynomial<'a, T, F>,
    polynomials: Vec<DivisionPolynomial<'a, T, NZ, F>>,
}

impl<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> DivisionPolynomialGenerator<'a, T, NZ, F> {
    pub fn new(curve: &'a WeierstrassEllipticCurve<T, NZ, F>) -> Option<Self> {
        let mut polys: Vec<DivisionPolynomial<T, NZ, F>> = Vec::with_capacity(4);
        let field = curve.get_field();

        let zero = field.additive_identity();
        let one = field.multiplicative_identity();
        let two = field.add(&one, &one);
        let three: T = field.add(&two, &one);
        let four = field.add(&three, &one);
        let five: T = field.add(&four, &one);
        let six: T = field.add(&five, &one);
        let eight = field.add(&four, &four);
        let twelve: T = field.add(&six, &six);
        let twenty: T = field.add(&eight, &twelve);

        let minus_four = field.additive_inverse(&four);

        let a_squared = field.mul(curve.param_a(), curve.param_a());
        let b_squared = field.mul(curve.param_b(), curve.param_b());

        let a_cubed = field.mul(&a_squared, curve.param_a());

        let half = field.multiplicative_inverse(&two)?;

        let poly_ring = PolynomialRing::new(field);

        let curve_rhs = Polynomial::new(
            field,
            vec![
                field.clone(curve.param_b()),
                field.clone(curve.param_a()),
                field.clone(&zero),
                field.clone(&one),
            ],
        );

        // ψ0 = 0
        polys.push(DivisionPolynomial::new(poly_ring.additive_identity(), 0, 0));

        // ψ1 = 1
        polys.push(DivisionPolynomial::new(
            poly_ring.multiplicative_identity(),
            0,
            1,
        ));

        // ψ2 = 2y = 2 y^2 / y = 2 (x^3 + ax + b) / y
        polys.push(DivisionPolynomial::new(
            Polynomial::new(
                field,
                vec![
                    field.mul(&two, curve.param_b()), // 2b
                    field.mul(&two, curve.param_a()), // 2a x
                    field.clone(&zero),               // 0  x^2
                    field.clone(&two),                // 2  x^3
                ],
            ),
            1,
            2,
        ));

        // ψ3 = 3 x^4 + 6a x^2 + 12b x - a^2
        polys.push(DivisionPolynomial::new(
            Polynomial::new(
                field,
                vec![
                    field.additive_inverse(&a_squared),  // - a^2
                    field.mul(&twelve, curve.param_b()), // 12b   x
                    field.mul(&six, curve.param_a()),    // 6a    x^2
                    field.clone(&zero),                  // 0     x^3
                    field.mul(&three, curve.param_a()),  // 3     x^4
                ],
            ),
            0,
            3,
        ));

        // ψ4 = 4y (x^6 + 5a x^4 + 20b x^3 - 5a^2 x^2 - 4ab x - (8B^2 + A^3))
        //    = 4 (x^6 + 5a x^4 + 20b x^3 - 5a^2 x^2 - 4ab x - (8B^2 + A^3)) (x^3 + ax + b) / y
        polys.push(DivisionPolynomial::new(
            Polynomial::new(field, vec![field.clone(&four)])
                .mul(&Polynomial::new(
                    field,
                    vec![
                        field
                            .additive_inverse(&field.add(&field.mul(&eight, &b_squared), &a_cubed)), // -(8B^2 + A^3)
                        field.mul(&minus_four, &field.mul(curve.param_a(), curve.param_b())), // -4ab x
                        field.additive_inverse(&field.mul(&five, &a_squared)), // -5a^2 x^2
                        field.mul(&twenty, curve.param_b()),                   // 20b x^3
                        field.mul(&five, curve.param_a()),                     // 5a x^4
                        field.clone(&zero),                                    // 0 x^5
                        field.clone(&one),                                     // 1 x^6
                    ],
                ))
                .mul(&curve_rhs),
            1,
            4,
        ));

        Some(Self {
            _phantom: PhantomData,
            poly_ring,
            field,
            polynomials: polys,
            half,
            curve,
            curve_rhs,
        })
    }

    fn compute_next(&mut self) {
        let target_n = self.polynomials.len();
        let m = target_n >> 1;
        if target_n % 2 == 1 {
            let pmm1 = &self.polynomials[m - 1];
            let pm = &self.polynomials[m];
            let pmp1 = &self.polynomials[m + 1];
            let pmp2 = &self.polynomials[m + 2];

            self.polynomials.push(
                pmp2.mul(pm)
                    .mul(pm)
                    .mul(pm)
                    .sub(&pmm1.mul(pmp1).mul(pmp1).mul(pmp1), &self)
                    .unwrap()
                    .simplify_ys(&self),
            )
        } else {
            let pmm2 = &self.polynomials[m - 2];
            let pmm1 = &self.polynomials[m - 1];
            let pm = &self.polynomials[m];
            let pmp1 = &self.polynomials[m + 1];
            let pmp2 = &self.polynomials[m + 2];

            let r_pol = pmp2
                .mul(pmm1)
                .mul(pmm1)
                .sub(&pmm2.mul(pmp1).mul(pmp1), &self)
                .unwrap();
            let l_pol = pm.div_2y(&self);

            self.polynomials.push(l_pol.mul(&r_pol).simplify_ys(&self));
        }
    }

    pub fn compute_until(&mut self, n: usize) {
        if n < self.polynomials.len() {
            // done
            return;
        }

        while self.polynomials.len() <= n {
            self.compute_next();
        }
    }
}

fn schoofs_iteration<'a, T: Debug, NZ: Debug, U: Debug, F: FiniteField<T, NZ, U>>(
    division_polys: &mut DivisionPolynomialGenerator<'a, T, NZ, F>,
    l: u32,
) -> u32 {
    division_polys.compute_until(l as usize);

    // TODO https://en.wikipedia.org/wiki/Schoof%27s_algorithm
    todo!()
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::algebra::modular::PrimeField;

    use rug::Integer;

    #[test]
    fn test_division_polynomial() {
        let field = PrimeField::new(Integer::from(19))
            .unwrap()
            .get_checked()
            .unwrap();

        let curve = WeierstrassEllipticCurve::create_curve(&field, 2.into(), 3.into()).unwrap();

        let mut polys = DivisionPolynomialGenerator::new(&curve).unwrap();
        polys.compute_until(10);

        dbg!(polys);
    }
}
