use std::{fmt::Debug, marker::PhantomData, sync::LazyLock};

use rug::Integer;

use crate::{
    algebra::{
        Field, Fraction, Group,
        modular::{PrimeField, PrimeFieldNonZeroInteger},
    },
    algorithms::diffie_hellman::DiffieHellmanCapable,
};

// y^2 = x^3 + ax + b
#[derive(Debug)]
pub struct WeierstrassEllipticCurve<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> {
    _phantom: PhantomData<NZ>,
    field: &'a F,
    a: T,
    b: T,
}

impl<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> WeierstrassEllipticCurve<'a, T, NZ, F> {
    pub fn create_curve(field: &'a F, a: T, b: T) -> Option<Self> {
        if field.characteristic() == 2 || field.characteristic() == 3 {
            return None;
        }
        if Self::singular(&field, &a, &b) {
            return None;
        }
        Some(Self {
            _phantom: PhantomData,
            field,
            a,
            b,
        })
    }

    pub fn get_field(&self) -> &'a F {
        self.field
    }

    pub fn param_a(&self) -> &T {
        &self.a
    }

    pub fn param_b(&self) -> &T {
        &self.b
    }

    fn singular(field: &F, a: &T, b: &T) -> bool {
        let a3 = field.mul(&field.mul(a, a), a);
        let b2 = field.mul(b, b);
        let four_a3 = field.repeated_addition(a3, &4.into());
        let twenty_seven_b2 = field.repeated_addition(b2, &27.into());
        let delta = field.add(&four_a3, &twenty_seven_b2);
        field.is_additive_identity(&delta)
    }

    pub fn get_point_at(&self, x: T, y: T) -> Result<WeierstrassEllipticCurvePoint<T>, (T, T)> {
        let y2 = self.field.mul(&y, &y);
        let x2 = self.field.mul(&x, &x);
        let x2pa = self.field.add(&x2, &self.a);
        let x3pax = self.field.mul(&x2pa, &x);
        let x3paxpb = self.field.add(&x3pax, &self.b);
        if self.field.eq(&y2, &x3paxpb) {
            Ok(WeierstrassEllipticCurvePoint::Point { x, y })
        } else {
            Err((x, y))
        }
    }

    pub fn get_point_at_infinity(&self) -> WeierstrassEllipticCurvePoint<T> {
        WeierstrassEllipticCurvePoint::Infinity
    }

    fn double_point(&self, x: &T, y: &T) -> WeierstrassEllipticCurvePoint<T> {
        if self.field.is_additive_identity(y) {
            WeierstrassEllipticCurvePoint::Infinity
        } else {
            let two_y = self.field.add(y, y);
            // Safe to unwrap as we have: y != 0 => two_y != 0
            let two_y = self.field.construct_non_zero(two_y).unwrap();
            let x_squared = self.field.mul(x, x);
            let three_x_squared = self.field.repeated_addition(x_squared, &3.into());
            let m = self
                .field
                .div(&self.field.add(&three_x_squared, &self.a), &two_y);
            let x3 = self
                .field
                .sub(&self.field.mul(&m, &m), &self.field.add(x, x));
            let y3 = self
                .field
                .sub(&self.field.mul(&m, &self.field.sub(x, &x3)), y);
            WeierstrassEllipticCurvePoint::Point { x: x3, y: y3 }
        }
    }

    fn add_points(&self, x1: &T, y1: &T, x2: &T, y2: &T) -> WeierstrassEllipticCurvePoint<T> {
        let dy = self.field.sub(y2, y1);
        let dx = self.field.sub(x2, x1);
        // Safe to unwrap as we have: x1 != x2 <=> dx != 0
        let dx = self.field.construct_non_zero(dx).unwrap();
        let m = self.field.div(&dy, &dx);
        let x3 = self
            .field
            .sub(&self.field.mul(&m, &m), &self.field.add(x1, x2));
        let y3 = self
            .field
            .sub(&self.field.mul(&m, &self.field.sub(x1, &x3)), y1);
        WeierstrassEllipticCurvePoint::Point { x: x3, y: y3 }
    }
}

impl<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> Group<WeierstrassEllipticCurvePoint<T>>
    for WeierstrassEllipticCurve<'a, T, NZ, F>
{
    fn group_exponent(&self) -> Option<Integer> {
        // not trivially computable
        None
    }

    fn eq_group(&self, other: &Self) -> bool {
        self.field.eq_field(other.field)
            && self.field.eq(&self.a, &other.a)
            && self.field.eq(&self.b, &other.b)
    }

    fn additive_identity(&self) -> WeierstrassEllipticCurvePoint<T> {
        self.get_point_at_infinity()
    }

    fn additive_inverse(
        &self,
        x: &WeierstrassEllipticCurvePoint<T>,
    ) -> WeierstrassEllipticCurvePoint<T> {
        match x {
            WeierstrassEllipticCurvePoint::Point { x, y } => WeierstrassEllipticCurvePoint::Point {
                x: self.field.clone(x),
                y: self.field.additive_inverse(y),
            },
            WeierstrassEllipticCurvePoint::Infinity => WeierstrassEllipticCurvePoint::Infinity,
        }
    }

    fn add(
        &self,
        p1: &WeierstrassEllipticCurvePoint<T>,
        p2: &WeierstrassEllipticCurvePoint<T>,
    ) -> WeierstrassEllipticCurvePoint<T> {
        match (p1, p2) {
            (WeierstrassEllipticCurvePoint::Infinity, WeierstrassEllipticCurvePoint::Infinity) => {
                WeierstrassEllipticCurvePoint::Infinity
            }
            (
                WeierstrassEllipticCurvePoint::Infinity,
                WeierstrassEllipticCurvePoint::Point { x, y },
            )
            | (
                WeierstrassEllipticCurvePoint::Point { x, y },
                WeierstrassEllipticCurvePoint::Infinity,
            ) => WeierstrassEllipticCurvePoint::Point {
                x: self.field.clone(x),
                y: self.field.clone(y),
            },
            (
                WeierstrassEllipticCurvePoint::Point { x: x1, y: y1 },
                WeierstrassEllipticCurvePoint::Point { x: x2, y: y2 },
            ) => {
                if self.field.eq(x1, x2) {
                    if self.field.eq(y1, y2) {
                        self.double_point(x1, y1)
                    } else {
                        // then y1 = -y2 because on construction of the curve we check that the field's characteristic is not 2, so the sum is the point at infinity
                        WeierstrassEllipticCurvePoint::Infinity
                    }
                } else {
                    self.add_points(x1, y1, x2, y2)
                }
            }
        }
    }

    fn clone(&self, x: &WeierstrassEllipticCurvePoint<T>) -> WeierstrassEllipticCurvePoint<T> {
        match x {
            WeierstrassEllipticCurvePoint::Point { x, y } => WeierstrassEllipticCurvePoint::Point {
                x: self.field.clone(x),
                y: self.field.clone(y),
            },
            WeierstrassEllipticCurvePoint::Infinity => WeierstrassEllipticCurvePoint::Infinity,
        }
    }

    fn eq(
        &self,
        x: &WeierstrassEllipticCurvePoint<T>,
        y: &WeierstrassEllipticCurvePoint<T>,
    ) -> bool {
        match (x, y) {
            (
                WeierstrassEllipticCurvePoint::Point { x: x1, y: y1 },
                WeierstrassEllipticCurvePoint::Point { x: x2, y: y2 },
            ) => self.field.eq(x1, x2) && self.field.eq(y1, y2),
            (WeierstrassEllipticCurvePoint::Infinity, WeierstrassEllipticCurvePoint::Infinity) => {
                true
            }
            _ => false,
        }
    }

    fn is_additive_identity(&self, x: &WeierstrassEllipticCurvePoint<T>) -> bool {
        match x {
            WeierstrassEllipticCurvePoint::Infinity => true,
            _ => false,
        }
    }
}

#[derive(Debug)]
pub enum WeierstrassEllipticCurvePoint<T> {
    Point { x: T, y: T },
    Infinity,
}

// b y^2 = x^3 + a x^2 + x
#[derive(Debug)]
pub struct MontgomeryEllipticCurve<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> {
    _phantom: PhantomData<NZ>,
    field: &'a F,
    a24: T,
    a: T,
    b: T,
}

impl<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> MontgomeryEllipticCurve<'a, T, NZ, F> {
    pub fn create_curve(field: &'a F, a: T, b: T) -> Option<Self> {
        if field.characteristic() == 2 || field.characteristic() == 3 {
            return None;
        }
        if Self::singular(&field, &a, &b) {
            return None;
        }

        let two = field.add(
            &field.multiplicative_identity(),
            &field.multiplicative_identity(),
        );
        let four = field.add(&two, &two);

        let fourth = field.multiplicative_inverse(&four)?;
        let a24 = field.mul(&field.add(&a, &two), &fourth);

        Some(Self {
            _phantom: PhantomData,
            field,
            a24,
            a,
            b,
        })
    }

    fn singular(field: &F, a: &T, b: &T) -> bool {
        // B(A^2 - 4) = 0 <=> B = 0 or A = +/- 2
        if field.is_additive_identity(b) {
            return true;
        }
        let one = field.multiplicative_identity();
        let two = field.add(&one, &one);
        field.eq(a, &two) || field.eq(a, &field.additive_inverse(&two))
    }

    pub fn reduced_eq(&self, p1: (&T, &T), p2: (&T, &T)) -> bool {
        self.field
            .eq(&self.field.mul(p1.0, p2.1), &self.field.mul(p1.1, p2.0))
    }

    pub fn to_xy(&self, p: &MontgomeryEllipticCurvePoint<T>) -> Option<(T, T)> {
        let z_inv = self.field.multiplicative_inverse(&p.z_proj)?;
        let x = self.field.mul(&p.x_proj, &z_inv);
        let y = self.field.mul(&p.y_proj, &z_inv);
        Some((x, y))
    }

    pub fn to_x(&self, x: &T, z: &T) -> Option<T> {
        let z_inv = self.field.multiplicative_inverse(z)?;
        let x = self.field.mul(x, &z_inv);
        Some(x)
    }

    pub fn xdbl(&self, x: &T, z: &T) -> (T, T) {
        let x_sum = self.field.add(x, z);
        let x_diff = self.field.sub(x, z);
        let x_sum_sqr = self.field.mul(&x_sum, &x_sum);
        let x_diff_sqr = self.field.mul(&x_diff, &x_diff);
        let four_x_z = self.field.sub(&x_sum_sqr, &x_diff_sqr);
        let new_x = self.field.mul(&x_sum_sqr, &x_diff_sqr);
        let term = self.field.mul(&self.a24, &four_x_z);
        let sum = self.field.add(&x_diff_sqr, &term);
        let new_z = self.field.mul(&four_x_z, &sum);
        (new_x, new_z)
    }

    pub fn xadd(&self, x_p: &T, z_p: &T, x_q: &T, z_q: &T, x_pq: &T, z_pq: &T) -> (T, T) {
        if self.field.is_additive_identity(z_p) {
            return (self.field.clone(x_q), self.field.clone(z_q));
        }
        if self.field.is_additive_identity(z_q) {
            return (self.field.clone(x_p), self.field.clone(z_p));
        }
        if self.field.is_additive_identity(z_pq) {
            return self.xdbl(x_p, z_p);
        }
        let xp_diff = self.field.sub(x_p, z_p);
        let xp_sum = self.field.add(x_p, z_p);
        let xq_diff = self.field.sub(x_q, z_q);
        let xq_sum = self.field.add(x_q, z_q);

        let term1 = self.field.mul(&xp_diff, &xq_sum);
        let term2 = self.field.mul(&xp_sum, &xq_diff);

        let xsum = self.field.add(&term1, &term2);
        let zdiff = self.field.sub(&term1, &term2);

        let xmul = self.field.mul(&xsum, &xsum);
        let zmul = self.field.mul(&zdiff, &zdiff);

        let new_x = self.field.mul(&z_pq, &xmul);
        let new_z = self.field.mul(&x_pq, &zmul);

        (new_x, new_z)
    }

    /// Adds two points in projective coordinates, returns the new point in projective coordinates
    pub fn xyadd(&self, x_1: &T, y_1: &T, z_1: &T, x_2: &T, y_2: &T, z_2: &T) -> (T, T, T) {
        if self.field.is_additive_identity(z_1) {
            return (
                self.field.clone(x_2),
                self.field.clone(y_2),
                self.field.clone(z_2),
            );
        }

        if self.field.is_additive_identity(z_2) {
            return (
                self.field.clone(x_1),
                self.field.clone(y_1),
                self.field.clone(z_1),
            );
        }

        let p1_x = Fraction::<T, NZ, F>::new(self.field.clone(x_1), self.field.clone(z_1));
        let p1_y = Fraction::<T, NZ, F>::new(self.field.clone(y_1), self.field.clone(z_1));
        let p2_x = Fraction::<T, NZ, F>::new(self.field.clone(x_2), self.field.clone(z_2));
        let p2_y = Fraction::<T, NZ, F>::new(self.field.clone(y_2), self.field.clone(z_2));

        let x_diff = p2_x.sub(&p1_x, &self.field);
        let y_diff = p2_y.sub(&p1_y, &self.field);

        let a = Fraction::new(
            self.field.clone(&self.a),
            self.field.multiplicative_identity(),
        );
        let b = Fraction::new(
            self.field.clone(&self.b),
            self.field.multiplicative_identity(),
        );

        let l = if x_diff.is_zero(&self.field) {
            if p1_y.is_zero(&self.field) {
                return self.get_point_at_infinity();
            }
            if y_diff.is_zero(&self.field) {
                // Double point
                let one = Fraction::<T, NZ, F>::new(
                    self.field.multiplicative_identity(),
                    self.field.multiplicative_identity(),
                );
                let two = one.add(&one, &self.field);
                let three = two.add(&one, &self.field);
                let x_squared = p1_x.mul(&p1_x, &self.field);
                let three_x_squared = x_squared.mul(&three, &self.field);
                let two_x = p1_x.mul(&two, &self.field);
                let two_a_x = a.mul(&two_x, &self.field);

                let l_num = three_x_squared
                    .add(&two_a_x, &self.field)
                    .add(&one, &self.field);
                let l_den = two.mul(&b, &self.field).mul(&p1_y, &self.field);

                l_num.div(&l_den, &self.field)
            } else {
                return self.get_point_at_infinity();
            }
        } else {
            y_diff.div(&x_diff, &self.field)
        };

        let l_squared = l.mul(&l, &self.field);
        let b_l_squared = b.mul(&l_squared, &self.field);

        let a_plus_x1_plus_x2 = a.add(&p1_x, &self.field).add(&p2_x, &self.field);

        let p3_x = b_l_squared.sub(&a_plus_x1_plus_x2, &self.field);

        let p3_y = l
            .mul(&p1_x.sub(&p3_x, &self.field), &self.field)
            .sub(&p1_y, &self.field);

        let x = self.field.mul(p3_x.get_num(), p3_y.get_den());
        let y = self.field.mul(p3_y.get_num(), p3_x.get_den());
        let z = self.field.mul(p3_x.get_den(), p3_y.get_den());

        (x, y, z)
    }

    pub fn get_point_at_infinity(&self) -> (T, T, T) {
        let MontgomeryEllipticCurvePoint {
            x_proj: x,
            y_proj: y,
            z_proj: z,
        } = self.additive_identity();
        (x, y, z)
    }

    pub fn ladder(&self, x: T, z: T, k: &Integer) -> (T, T) {
        let mut r0 = (
            self.field.multiplicative_identity(),
            self.field.additive_identity(),
        ); // point at infinity, R0 = 0*P
        let mut r1 = (self.field.clone(&x), self.field.clone(&z)); // R1 = 1*P = P

        let nbits = k.significant_bits(); // number of bits in k

        for i in (0..nbits).rev() {
            // r1 - r0 = P <=> r1 = r0 + P
            if !k.get_bit(i) {
                // r1 = r1 + r0 = 2r0 + P
                // r0 = 2r0
                // invariant: r1 = r0 + P preserved
                r1 = self.xadd(&r0.0, &r0.1, &r1.0, &r1.1, &x, &z);
                r0 = self.xdbl(&r0.0, &r0.1)
            } else {
                // r0 = r0 + r1 = 2r0 + P
                // r1 = 2r1 = 2(r0 + P) = 2r0 + 2P
                // invariant: r0 = r1 + P preserved
                r0 = self.xadd(&r1.0, &r1.1, &r0.0, &r0.1, &x, &z);
                r1 = self.xdbl(&r1.0, &r1.1);
            }
        }

        r0
    }

    // x^3 + ax^2 + x = ((x+a)x^2 + x
    pub fn get_point_at(&self, x: T, y: T) -> Option<MontgomeryEllipticCurvePoint<T>> {
        let y2 = self.field.mul(&y, &y);
        let by2 = self.field.mul(&self.b, &y2);
        let xpa = self.field.add(&x, &self.a);
        let xpa_x = self.field.mul(&xpa, &x);
        let xpa_x2 = self.field.mul(&xpa_x, &x);
        let rhs = self.field.add(&xpa_x2, &x);
        if self.field.eq(&by2, &rhs) {
            Some(MontgomeryEllipticCurvePoint {
                x_proj: x,
                y_proj: y,
                z_proj: self.field.multiplicative_identity(),
            })
        } else {
            None
        }
    }
}

#[derive(Debug)]
pub struct MontgomeryEllipticCurvePoint<T> {
    x_proj: T,
    y_proj: T,
    z_proj: T,
}

impl<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> Group<MontgomeryEllipticCurvePoint<T>>
    for MontgomeryEllipticCurve<'a, T, NZ, F>
{
    fn group_exponent(&self) -> Option<Integer> {
        // not trivially computable
        None
    }

    fn additive_identity(&self) -> MontgomeryEllipticCurvePoint<T> {
        MontgomeryEllipticCurvePoint {
            x_proj: self.field.additive_identity(),
            y_proj: self.field.multiplicative_identity(),
            z_proj: self.field.additive_identity(),
        }
    }

    fn eq_group(&self, other: &Self) -> bool {
        self.field.eq_field(other.field)
            && self.field.eq(&self.a, &other.a)
            && self.field.eq(&self.b, &other.b)
    }

    fn add(
        &self,
        p1: &MontgomeryEllipticCurvePoint<T>,
        p2: &MontgomeryEllipticCurvePoint<T>,
    ) -> MontgomeryEllipticCurvePoint<T> {
        if self.field.is_additive_identity(&p1.z_proj) {
            self.clone(p2)
        } else if self.field.is_additive_identity(&p2.z_proj) {
            self.clone(p1)
        } else {
            let (x1, y1, z1) = self.xyadd(
                &p1.x_proj, &p1.y_proj, &p1.z_proj, &p2.x_proj, &p2.y_proj, &p2.z_proj,
            );
            MontgomeryEllipticCurvePoint {
                x_proj: x1,
                y_proj: y1,
                z_proj: z1,
            }
        }
    }

    fn additive_inverse(
        &self,
        p: &MontgomeryEllipticCurvePoint<T>,
    ) -> MontgomeryEllipticCurvePoint<T> {
        MontgomeryEllipticCurvePoint {
            x_proj: self.field.clone(&p.x_proj),
            y_proj: self.field.additive_inverse(&p.y_proj),
            z_proj: self.field.clone(&p.z_proj),
        }
    }

    fn clone(&self, p: &MontgomeryEllipticCurvePoint<T>) -> MontgomeryEllipticCurvePoint<T> {
        MontgomeryEllipticCurvePoint {
            x_proj: self.field.clone(&p.x_proj),
            y_proj: self.field.clone(&p.y_proj),
            z_proj: self.field.clone(&p.z_proj),
        }
    }

    fn eq(
        &self,
        p1: &MontgomeryEllipticCurvePoint<T>,
        p2: &MontgomeryEllipticCurvePoint<T>,
    ) -> bool {
        // x1 / z1 = x2 / z2 <=> x1 * z2 = x2 * z1
        // y1 / z1 = y2 / z2 <=> y1 * z2 = y2 * z1
        self.field.eq(
            &self.field.mul(&p1.x_proj, &p2.z_proj),
            &self.field.mul(&p2.x_proj, &p1.z_proj),
        ) && self.field.eq(
            &self.field.mul(&p1.y_proj, &p2.z_proj),
            &self.field.mul(&p2.y_proj, &p1.z_proj),
        )
    }

    fn is_additive_identity(&self, x: &MontgomeryEllipticCurvePoint<T>) -> bool {
        self.field.is_additive_identity(&x.z_proj)
    }
}

impl<'a, T: Debug, NZ: Debug, F: Field<T, NZ>> DiffieHellmanCapable<(T, T)>
    for MontgomeryEllipticCurve<'a, T, NZ, F>
{
    fn dh(&self, a: (T, T), b: &Integer) -> (T, T) {
        self.ladder(a.0, a.1, b)
    }
}

#[cfg(test)]
mod tests {
    use rayon::iter::{IntoParallelIterator, ParallelIterator};
    use rug::Integer;

    use crate::{
        algebra::{CompleteRing, Group, Ring, modular::PrimeField},
        structures::curves::elliptic::{
            MontgomeryEllipticCurve, WeierstrassEllipticCurve, WeierstrassEllipticCurvePoint,
        },
    };

    #[test]
    pub fn test_weierstrass_curve17() {
        let field = PrimeField::new(Integer::from(17))
            .unwrap()
            .get_checked()
            .unwrap();

        // y^2 = x^3 + x + 1 over F_17
        let curve =
            WeierstrassEllipticCurve::create_curve(&field, Integer::from(1), Integer::from(1))
                .unwrap();

        let test_data = &[
            ((-8, 5), (4, -1), (0, -1)),
            ((-8, 5), (-7, -5), (-4, 1)),
            ((-2, -5), (4, 1), (-1, 4)),
            ((4, 1), (-4, -1), (-1, -4)),
            ((-7, 5), (-1, 4), (0, -1)),
        ];

        for ((x1, y1), (x2, y2), (x3, y3)) in test_data {
            let p1 = curve.get_point_at((*x1).into(), (*y1).into()).unwrap();
            let p2 = curve.get_point_at((*x2).into(), (*y2).into()).unwrap();
            let p3 = curve.get_point_at((*x3).into(), (*y3).into()).unwrap();
            let sum = curve.add(&p1, &p2);
            assert!(
                curve.eq(&sum, &p3),
                "sum of ({}, {}) and ({}, {}) should be ({}, {}), found {:?}",
                x1,
                y1,
                x2,
                y2,
                x3,
                y3,
                sum
            );
        }
    }

    #[test]
    pub fn test_montgomery_curve53() {
        let field = PrimeField::new(Integer::from(53))
            .unwrap()
            .get_checked()
            .unwrap();

        // y^2 = x^3 + x over F_53
        let curve =
            MontgomeryEllipticCurve::create_curve(&field, Integer::from(0), Integer::from(1))
                .unwrap();

        let test_data = &[
            ((-17, 23), (-13, -4), (6, 13)),
            ((9, -7), (13, 14), (-11, 6)),
            ((-6, -19), (-4, -12), (9, -7)),
            ((5, -17), (26, 18), (13, -14)),
        ];

        for ((x1, y1), (x2, y2), (x3, y3)) in test_data {
            let p1 = curve.get_point_at((*x1).into(), (*y1).into()).unwrap();
            let p2 = curve.get_point_at((*x2).into(), (*y2).into()).unwrap();
            let p3 = curve.get_point_at((*x3).into(), (*y3).into()).unwrap();
            let sum = curve.add(&p1, &p2);

            let z_inv = curve.field.multiplicative_inverse(&sum.z_proj).unwrap();
            let x = curve.field.mul(&z_inv, &sum.x_proj);
            let y = curve.field.mul(&z_inv, &sum.y_proj);

            assert!(
                curve.eq(&sum, &p3),
                "sum of ({}, {}) and ({}, {}) should be ({}, {}), found ({}, {}, {}) -> ({}, {})",
                x1,
                y1,
                x2,
                y2,
                x3,
                y3,
                sum.x_proj,
                sum.y_proj,
                sum.z_proj,
                x,
                y
            );
        }
    }

    #[test]
    fn test_montgomery_ladder() {
        let field = PrimeField::new(9973.into()).unwrap().get_checked().unwrap();

        // By^2 = x^3 + Ax^2 + x over F_9973, A = 0, B = 1 --> y^2 = x^3 + x
        let curve_m =
            MontgomeryEllipticCurve::create_curve(&field, Integer::from(0), Integer::from(1))
                .unwrap();

        // y^2 = x^3 + Ax + B over F_9973, A = 1, B = 0 --> y^2 = x^3 + x
        let curve_w =
            WeierstrassEllipticCurve::create_curve(&field, Integer::from(1), Integer::from(0))
                .unwrap();

        (0..9973i64).into_par_iter().for_each(|x| {
            let rhs = x * x * x + x;
            for y in (0..9973).filter(|y| (rhs - y * y) % 9973 == 0) {
                let point_m = curve_m.get_point_at(x.into(), y.into()).unwrap();
                let point_w = curve_w.get_point_at(x.into(), y.into()).unwrap();

                for n in 1..100 {
                    let point_m_n = curve_m.repeated_addition(curve_m.clone(&point_m), &n.into());
                    let point_w_n = curve_w.repeated_addition(curve_w.clone(&point_w), &n.into());
                    let x_n: (Integer, Integer) = curve_m.ladder(x.into(), 1.into(), &n.into());

                    let Some(z1_inv) = field.multiplicative_inverse(&point_m_n.z_proj) else {
                        assert!(
                            matches!(point_w_n, WeierstrassEllipticCurvePoint::Infinity)
                                && field.is_additive_identity(&x_n.1),
                            "point_m_n.z_proj should not be zero when the result is not the point at infinity, x: {}, y: {}, n: {}, point_m: {:?}, point_w: {:?}, point_m_n: {:?}, point_w_n: {:?}, x_n: {:?}",
                            x,
                            y,
                            n,
                            point_m,
                            point_w,
                            point_m_n,
                            point_w_n,
                            x_n
                        );
                        continue;
                    };
                    let x1 = field.mul(&z1_inv, &point_m_n.x_proj);
                    let y1 = field.mul(&z1_inv, &point_m_n.y_proj);

                    let Some(z2_inv) = field.multiplicative_inverse(&x_n.1) else {
                        // Already checked higher up that point_m_n.z_proj != 0, so we have contradictory results --> panic !
                        panic!(
                            "x_n.1 should not be zero when the result is not the point at infinity, x: {}, y: {}, n: {}, point_m: {:?}, point_w: {:?}, point_m_n: {:?}, point_w_n: {:?}, x_n: {:?}",
                            x, y, n, point_m, point_w, point_m_n, point_w_n, x_n
                        );
                    };
                    let x2 = field.mul(&z2_inv, &x_n.0);

                    match &point_w_n {
                        WeierstrassEllipticCurvePoint::Point { x: x3, y: y3 } => {
                            assert!(
                                (x1 == x2) && (&x1 == x3) && (&y1 == y3),
                                "Contradictory results: x: {}, y: {}, n: {}, point_m: {:?}, point_w: {:?}, point_m_n: {:?}, point_w_n: {:?}, x_n: {:?}, x1: {}, y1: {}, x2: {}, x3: {}, y3: {}",
                                x,
                                y,
                                n,
                                point_m,
                                point_w,
                                point_m_n,
                                point_w_n,
                                x_n,
                                x1,
                                y1,
                                x2,
                                x3,
                                y3
                            );
                        }
                        WeierstrassEllipticCurvePoint::Infinity => {
                            panic!(
                                "point_w_n should not be infinity, x: {}, y: {}, n: {}, point_m: {:?}, point_w: {:?}, point_m_n: {:?}, point_w_n: {:?}, x_n: {:?}, x1: {}, y1: {}, x2: {}",
                                x, y, n, point_m, point_w, point_m_n, point_w_n, x_n, x1, y1, x2
                            );
                        }
                    }
                }
            }
        });
    }
}

// SAFETY: 2^255 - 19 is verified to be definitely prime
static P_25519_FIELD: LazyLock<PrimeField> = LazyLock::new(|| unsafe {
    PrimeField::new((Integer::from(1) << 255) - Integer::from(19))
        .unwrap()
        .unwrap()
        .unwrap()
});

pub fn get_curve25519()
-> MontgomeryEllipticCurve<'static, Integer, PrimeFieldNonZeroInteger, PrimeField> {
    MontgomeryEllipticCurve::create_curve(&*P_25519_FIELD, Integer::from(486662), Integer::from(1))
        .unwrap()
}
