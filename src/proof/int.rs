use std::cmp::{Ord, Ordering, PartialOrd};
use std::convert::From;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Rem, Sub};

#[derive(Debug, Clone, PartialEq, Eq, Copy)]
pub enum Int {
    Infinity,
    NegInfinity,
    I(i128),
}

// TODO Exaplain VERY CLEARLY
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct EvalInt {
    val: Int,
    bit_more: bool,
    bit_less: bool,
}

/// Unbounded rational number.
#[derive(Debug, Clone, Copy)]
pub struct Rational {
    pub numerator: Int,
    pub denominator: Int,
}

impl Int {
    pub const ZERO: Int = Int::I(0);
    pub const ONE: Int = Int::I(1);
    pub const MINUS_ONE: Int = Int::I(-1);

    /// Returns true iff self is not Infinity or -Infinity
    pub fn is_finite(&self) -> bool {
        use Int::{Infinity, NegInfinity, I};
        match self {
            I(_) => true,
            Infinity | NegInfinity => false,
        }
    }
}

impl EvalInt {
    pub const ZERO: EvalInt = EvalInt {
        val: Int::ZERO,
        bit_more: false,
        bit_less: false,
    };

    pub const ONE: EvalInt = EvalInt {
        val: Int::ONE,
        bit_more: false,
        bit_less: false,
    };

    pub const BIT_LESS: EvalInt = EvalInt {
        val: Int::ZERO,
        bit_less: true,
        bit_more: false,
    };

    pub const BIT_MORE: EvalInt = EvalInt {
        val: Int::ZERO,
        bit_more: true,
        bit_less: false,
    };

    pub fn as_lower_bound(&self) -> Int {
        if self.bit_more && !self.bit_less {
            self.val + Int::ONE
        } else if !self.bit_more && self.bit_less {
            self.val // - Int::ONE
        } else {
            self.val
        }
    }

    pub fn as_upper_bound(&self) -> Int {
        if self.bit_less && !self.bit_more {
            self.val - Int::ONE
        } else if !self.bit_less && self.bit_more {
            self.val // + Int::ONE
        } else {
            self.val
        }
    }

    pub fn is_finite(&self) -> bool {
        self.val.is_finite()
    }

    pub fn is_exact(&self) -> bool {
        !self.bit_more && !self.bit_less
    }
}

impl Rational {
    pub const ZERO: Rational = Rational {
        numerator: Int::ZERO,
        denominator: Int::ONE,
    };
    pub const ONE: Rational = Rational {
        numerator: Int::ONE,
        denominator: Int::ONE,
    };
    pub const MINUS_ONE: Rational = Rational {
        numerator: Int::MINUS_ONE,
        denominator: Int::ONE,
    };
    pub const INFINITY: Rational = Rational {
        numerator: Int::Infinity,
        denominator: Int::ONE,
    };

    /// Returns 1/x
    pub fn recip(x: Int) -> Rational {
        Rational {
            numerator: Int::ONE,
            denominator: x,
        }
    }

    /// Returns true iff self == 0
    ///
    /// self == 0 iff it is in the form 0/x where x != 0
    pub fn is_zero(&self) -> bool {
        self.numerator == Int::ZERO && self.denominator != Int::ZERO
    }

    pub fn simplify(mut self) -> Rational {
        if self.numerator == Int::ZERO {
            if self.denominator == Int::ZERO {
                // We'll erm... just... leave 0/0?
                return self;
            }
            // 0/x = 0
            return Rational::ZERO;
        }
        if self.denominator == Int::ZERO {
            // x/0 = Infinity
            return Rational::from(Int::Infinity * self.sign_int());
        }
        // Cancel negatives
        if self.denominator < Int::ZERO && self.numerator < Int::ZERO {
            self.numerator = -self.numerator;
            self.denominator = -self.denominator;
        }
        // Do the division if it's exact!
        if self.numerator % self.denominator == Int::ZERO {
            return Rational::from(self.numerator / self.denominator);
        }
        if self.denominator % self.numerator == Int::ZERO {
            return Rational::recip(self.denominator / self.numerator);
        }
        self
    }

    /// Evaluate the rational number, rounding down (not towards 0, down).
    /// If the division is not exact, the returned EvalInt will contain the relivent epsilon/delta.
    pub fn eval_floor(self) -> EvalInt {
        EvalInt::from(self.numerator).div_floor(self.denominator.into())
    }

    /// Evaluate the rational number, rounding up (not away from 0, up).
    /// If the division is not exact, the returned EvalInt will contain the relivent epsilon/delta.
    pub fn eval_ceil(self) -> EvalInt {
        EvalInt::from(self.numerator).div_ceil(self.denominator.into())
    }
}

impl<T: Into<i128>> From<T> for Int {
    fn from(x: T) -> Int {
        Int::I(x.into())
    }
}

impl<T: Into<i128>> From<T> for EvalInt {
    fn from(x: T) -> EvalInt {
        Int::I(x.into()).into()
    }
}

impl From<Int> for EvalInt {
    fn from(x: Int) -> EvalInt {
        EvalInt {
            val: x,
            bit_more: false,
            bit_less: false,
        }
    }
}

impl From<Int> for Rational {
    fn from(x: Int) -> Rational {
        Rational {
            numerator: x,
            denominator: Int::ONE,
        }
    }
}

impl Ord for Int {
    fn cmp(&self, other: &Int) -> Ordering {
        use Int::{Infinity, NegInfinity, I};
        match (self, other) {
            (I(x), I(y)) => x.cmp(y),
            (Infinity, Infinity) => Ordering::Equal,
            (NegInfinity, Infinity) => Ordering::Less,
            (NegInfinity, NegInfinity) => Ordering::Equal,
            (Infinity, NegInfinity) => Ordering::Greater,
            (I(_), Infinity) => Ordering::Less,
            (NegInfinity, I(_)) => Ordering::Less,
            (Infinity, I(_)) => Ordering::Greater,
            (I(_), NegInfinity) => Ordering::Greater,
        }
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, other: &Int) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for Rational {
    fn eq(&self, other: &Rational) -> bool {
        (*self - *other).is_zero()
    }
}

impl Eq for Rational {}

impl Ord for Rational {
    fn cmp(&self, other: &Rational) -> Ordering {
        match (*self - *other).sign_i8() {
            -1 => Ordering::Less,
            0 => Ordering::Equal,
            1 => Ordering::Greater,

            _ => panic!("invalid sign"),
        }
    }
}

impl PartialOrd for Rational {
    fn partial_cmp(&self, other: &Rational) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Neg for Int {
    type Output = Int;
    fn neg(self) -> Int {
        use Int::{Infinity, NegInfinity, I};
        match self {
            Infinity => NegInfinity,
            NegInfinity => Infinity,
            I(x) => I(-x),
        }
    }
}

impl Add for Int {
    type Output = Int;
    fn add(self, rhs: Int) -> Int {
        use Int::{Infinity, NegInfinity, I};
        match (&self, &rhs) {
            (Infinity, Infinity) => Infinity,
            (Infinity, I(_)) => Infinity,
            (I(_), Infinity) => Infinity,
            (NegInfinity, NegInfinity) => NegInfinity,
            (NegInfinity, I(_)) => NegInfinity,
            (I(_), NegInfinity) => NegInfinity,
            (I(x), I(y)) => I(x + y),
            (Infinity, NegInfinity) | (NegInfinity, Infinity) => {
                panic!(format!("cannot add {} to {}", rhs, self))
            }
        }
    }
}

impl Sub for Int {
    type Output = Int;
    fn sub(self, rhs: Int) -> Int {
        use Int::{Infinity, NegInfinity, I};
        match (&self, &rhs) {
            (Infinity, NegInfinity) => Infinity,
            (NegInfinity, Infinity) => NegInfinity,
            (Infinity, I(_)) => Infinity,
            (I(_), Infinity) => Infinity,
            (NegInfinity, I(_)) => NegInfinity,
            (I(_), NegInfinity) => NegInfinity,
            (I(x), I(y)) => I(x - y),
            (Infinity, Infinity) | (NegInfinity, NegInfinity) => {
                panic!(format!("cannot sub {} from {}", rhs, self))
            }
        }
    }
}

impl Mul for Int {
    type Output = Int;
    fn mul(self, rhs: Int) -> Int {
        use Int::{Infinity, NegInfinity, I};
        match (&self, &rhs) {
            (Infinity, Infinity) => Infinity,
            (NegInfinity, NegInfinity) => Infinity,
            (Infinity, NegInfinity) => NegInfinity,
            (NegInfinity, Infinity) => NegInfinity,

            (I(x), I(y)) => I(x * y),

            (Infinity, I(x)) | (I(x), Infinity) => {
                if *x > 0 {
                    Infinity
                } else if *x < 0 {
                    NegInfinity
                } else {
                    I(0)
                }
            }

            (NegInfinity, I(x)) | (I(x), NegInfinity) => {
                if *x > 0 {
                    NegInfinity
                } else if *x < 0 {
                    Infinity
                } else {
                    I(0)
                }
            }
        }
    }
}

impl Div for Int {
    type Output = Int;
    /// Integer division. The result is rounded towards 0.
    fn div(self, rhs: Int) -> Int {
        use Int::{Infinity, NegInfinity, I};
        match (&self, &rhs) {
            (num, I(0)) => {
                if *num > Int::ZERO {
                    Int::Infinity
                } else if *num < Int::ZERO {
                    Int::NegInfinity
                } else {
                    panic!("0/0")
                }
            }

            (I(x), I(y)) => I(x / y),

            (I(_), Infinity) | (I(_), NegInfinity) => I(0),

            (Infinity, I(x)) => {
                if *x > 0 {
                    Infinity
                } else if *x < 0 {
                    NegInfinity
                } else {
                    panic!("divide by 0")
                }
            }

            (NegInfinity, I(x)) => {
                if *x > 0 {
                    NegInfinity
                } else if *x < 0 {
                    Infinity
                } else {
                    panic!("divide by 0")
                }
            }

            (Infinity, Infinity)
            | (Infinity, NegInfinity)
            | (NegInfinity, Infinity)
            | (NegInfinity, NegInfinity) => panic!(format!("cannot divide {} by {}", self, rhs)),
        }
    }
}

impl Rem for Int {
    type Output = Int;
    fn rem(self, rhs: Int) -> Int {
        use Int::{Infinity, NegInfinity, I};
        match (&self, &rhs) {
            (_, I(0)) => panic!("mod by 0"),

            (I(x), I(y)) => I(x % y),

            (I(x), Infinity) | (I(x), NegInfinity) => I(*x),

            (Infinity, I(_)) => panic!("mod of infinity"),
            (NegInfinity, I(_)) => panic!("mod of -infinity"),

            (Infinity, Infinity)
            | (Infinity, NegInfinity)
            | (NegInfinity, Infinity)
            | (NegInfinity, NegInfinity) => panic!(format!("cannot mod {} with {}", self, rhs)),
        }
    }
}

impl Int {
    /// Divide and round up
    pub fn div_ceil(self, rhs: Int) -> Int {
        let result = self / rhs;
        if rhs != Int::ZERO && self % rhs != Int::ZERO {
            let final_sign = self.sign_i8() * rhs.sign_i8();
            match final_sign {
                // rounding towards 0 is down so we need to add 1
                1 => return result + Int::ONE,
                // the result was 0
                0 => (),
                // rounding towards 0 was up!
                -1 => (),

                _ => panic!("invalid sign"),
            }
        }
        result
    }

    /// Divide and round down
    pub fn div_floor(self, rhs: Int) -> Int {
        let result = self / rhs;
        if rhs != Int::ZERO && self % rhs != Int::ZERO {
            let final_sign = self.sign_i8() * rhs.sign_i8();
            match final_sign {
                // rounding towards 0 was down!
                1 => (),
                // the result was 0
                0 => (),
                // rounding towards 0 was up, so subtract 1
                -1 => return result - Int::ONE,

                _ => panic!("invalid sign"),
            }
        }
        result
    }

    /// Returns:
    /// -  1 if self > 0
    /// -  0 if self = 0
    /// - -1 if self < =
    pub fn signnum(&self) -> Int {
        match self.cmp(&Int::ZERO) {
            Ordering::Less => -Int::ONE,
            Ordering::Equal => Int::ZERO,
            Ordering::Greater => Int::ONE,
        }
    }

    /// Returns:
    /// -  1 if self > 0
    /// -  0 if self = 0
    /// - -1 if self < =
    pub fn sign_i8(&self) -> i8 {
        match self.cmp(&Int::ZERO) {
            Ordering::Less => -1,
            Ordering::Equal => 0,
            Ordering::Greater => 1,
        }
    }
}

impl Neg for EvalInt {
    type Output = EvalInt;
    fn neg(self) -> EvalInt {
        EvalInt {
            val: -self.val,
            bit_more: self.bit_less,
            bit_less: self.bit_more,
        }
    }
}

impl Add for EvalInt {
    type Output = EvalInt;
    fn add(self, rhs: EvalInt) -> EvalInt {
        EvalInt {
            val: self.val + rhs.val,
            bit_more: self.bit_more || rhs.bit_more,
            bit_less: self.bit_less || rhs.bit_less,
        }
    }
}

impl Sub for EvalInt {
    type Output = EvalInt;
    fn sub(self, rhs: EvalInt) -> EvalInt {
        // TODO Maybe optimise? I'm keeping it simple for now.
        self + (-rhs)
    }
}

impl Mul for EvalInt {
    type Output = EvalInt;
    fn mul(self, rhs: EvalInt) -> EvalInt {
        if self.is_exact() {
            if self.val < Int::ZERO {
                // Let's make sure that lhs is positive
                return (-self).mul(-rhs);
            } else if self.val == Int::ZERO {
                // 0*x = 0
                return EvalInt::ZERO;
            }
            // So now it's a positive exact number multiplied by something!
            return EvalInt {
                val: self.val * rhs.val,
                bit_more: rhs.bit_more,
                bit_less: rhs.bit_less,
            };
        } else if rhs.is_exact() {
            return rhs.mul(self);
        }

        // Neither is exact... But...

        if self.val == Int::ZERO {
            todo!();
        } else if rhs.val == Int::ZERO {
            return rhs.mul(self);
        }

        // self*rhs = (self.val + self.e - self.d)*rhs
        //          = self.val*rhs + self.e*rhs - self.d*rhs
        return EvalInt::from(self.val) * rhs
            + if self.bit_more {
                EvalInt::BIT_MORE * rhs
            } else {
                EvalInt::ZERO
            }
            + if self.bit_less {
                EvalInt::BIT_LESS * rhs
            } else {
                EvalInt::ZERO
            };

        // TODO Below is the start of a probably more improved version.
        // It's more effort though.
        // (self + self.e - self.d)(rhs + rhs.e - rhs.d)
        // = self*rhs + self*rhs.e - self*rhs.d
        //   + self.e*rhs + self.e*rhs.e - self.e*rhs.d
        //   - self.d*rhs  - self.d*rhs.e + self.d*rhs.d
        // self > 0 && rhs > 0
        //  = self*rhs
        //    + self*rhs.e + self.e*rhs + self.e*rhs.e + self.d*rhs.d
        //    - self*rhs.d - self.d*rhs - self.e*rhs.d - self.d*rhs.e
        // self == 0 && rhs > 0
        //  = 0
        //    + self.e*rhs + self.e*rhs.e + self.d*rhs.d
        //    - self.d*rhs - self.e*rhs.d - self.d*rhs.e
        // self > 0 && rhs == 0
        //  = 0
        //    + self*rhs.e + self.e*rhs.e + self.d*rhs.d
        //    - self*rhs.d - self.e*rhs.d - self.d*rhs.e
        //
        // self < 0 && rhs < 0
        //  = self*rhs
        //    - (-self)*rhs.e - self.e*(-rhs) + self.e*rhs.e + self.d*rhs.d
        //    + (-self)*rhs.d + self.d*(-rhs) - self.e*rhs.d - self.d*rhs.e
        //  = self*rhs
        //    + (-self)*rhs.d + self.d*(-rhs) + self.e*rhs.e + self.d*rhs.d
        //    - (-self)*rhs.e - self.e*(-rhs) - self.e*rhs.d - self.d*rhs.e
        // self == 0 && rhs > 0
        //  = 0
        //    - self.e*(-rhs) + self.e*rhs.e + self.d*rhs.d
        //    + self.d*(-rhs) - self.e*rhs.d - self.d*rhs.e
        //  = 0
        //    + self.d*(-rhs) + self.e*rhs.e + self.d*rhs.d
        //    - self.e*(-rhs) - self.e*rhs.d - self.d*rhs.e
        // self > 0 && rhs == 0
        //  = 0
        //    - (-self)*rhs.e + self.e*rhs.e + self.d*rhs.d
        //    + (-self)*rhs.d - self.e*rhs.d - self.d*rhs.e
        //  = 0
        //    + (-self)*rhs.d + self.e*rhs.e + self.d*rhs.d
        //    - (-self)*rhs.e - self.e*rhs.d - self.d*rhs.e
        //
        // self > 0 && rhs > 0
        //  = self*rhs
        //    + rhs.e || self.e
        //    - rhs.d || self.d
        // self == 0 && rhs > 0
        //  = 0
        //    + self.e || self.d && rhs.d
        //    - self.d || self.e && rhs.d
        // self > 0 && rhs == 0
        //  = 0
        //    + rhs.e || self.d && rhs.d
        //    - rhs.d || self.d && rhs.e
        //
        // self < 0 && rhs < 0
        //  = self*rhs
        //    + rhs.d || self.d || self.e && rhs.e || self.d && rhs.d
        //    + (-self)*rhs.d + self.d*(-rhs) + self.e*rhs.e + self.d*rhs.d
        //    - (-self)*rhs.e - self.e*(-rhs) - self.e*rhs.d - self.d*rhs.e
        // self == 0 && rhs > 0
        //  = 0
        //    + self.d || self.e && rhs.e
        //    + self.e || self.d && rhs.d
        // self > 0 && rhs == 0
        //  = 0
        //    + rhs.d || self.e && rhs.e
        //    - rhs.e || self.e && rhs.d
        //

        /*
        let bit_more;
        let bit_less;

        if self.val > Int::ZERO && rhs.val > Int::ZERO {
            bit_more = self.bit_more || rhs.bit_more;
            bit_less = self.bit_less || rhs.bit_less;
        } else if self.val == Int::ZERO && rhs.val > Int::ZERO {
            bit_more = self.bit_more || self.bit_less && rhs.bit_less;
            bit_less = self.bit_less || self.bit_more && rhs.bit_less;
        } else if self.val > Int::ZERO && rhs.val == Int::ZERO {
            bit_more = rhs.bit_more || self.bit_less && rhs.bit_less;
            bit_less = rhs.bit_less || self.bit_less && rhs.bit_more;
        } else if self.val < Int::ZERO && rhs.val < Int::ZERO {
            bit_more = rhs.bit_more || self.bit_less && self.bit_less;
            bit_less = rhs.bit_less || self.bit_less && rhs.bit_more;
        } else if self.val == Int::ZERO && rhs.val == Int::ZERO {
            bit_more = rhs.bit_more || self.bit_less && self.bit_less;
            bit_less = rhs.bit_less || self.bit_less && rhs.bit_more;
        }

        EvalInt {
            val: self.val * rhs.val,
            bit_more: true,
            bit_less: true,
        }
        */
    }
}

/*
Commented since this may not be the expected behaviour.
impl Div for EvalInt {
    type Output = EvalInt;
    /// Integer division. The result is floored.
    fn div(self, rhs: EvalInt) -> EvalInt {
        self.div_floor(rhs)
    }
}
*/

// FIXME Signs...
impl EvalInt {
    /// Divide and round up
    pub fn div_ceil(self, rhs: EvalInt) -> EvalInt {
        if self.is_exact() && !rhs.is_exact() {
            todo!();
        } else if rhs.is_exact() {
            return EvalInt {
                val: self.val.div_ceil(rhs.val),
                bit_more: self.bit_more,
                bit_less: self.bit_less
                    || (rhs.val != Int::ZERO || self.val % rhs.val != Int::ZERO),
            };
        }
        todo!();

        EvalInt {
            val: self.val.div_ceil(rhs.val),
            bit_more: self.bit_more || rhs.bit_less,
            bit_less: self.bit_less
                || rhs.bit_more
                || (rhs.val != Int::ZERO || self.val % rhs.val != Int::ZERO),
        }
    }

    /// Divide and round down
    pub fn div_floor(self, rhs: EvalInt) -> EvalInt {
        if self.is_exact() && !rhs.is_exact() {
            todo!();
        } else if rhs.is_exact() {
            return EvalInt {
                val: self.val.div_floor(rhs.val),
                bit_more: self.bit_more
                    || (rhs.val != Int::ZERO && self.val % rhs.val != Int::ZERO),
                bit_less: self.bit_less,
            };
        }
        todo!();

        EvalInt {
            val: self.val.div_floor(rhs.val),
            bit_more: self.bit_more
                || rhs.bit_less
                || (rhs.val != Int::ZERO && self.val % rhs.val != Int::ZERO),
            bit_less: self.bit_less || rhs.bit_more,
        }
    }
}

impl Neg for Rational {
    type Output = Rational;
    fn neg(self) -> Rational {
        Rational {
            numerator: -self.numerator,
            denominator: self.denominator,
        }
    }
}

impl Add for Rational {
    type Output = Rational;
    fn add(self, rhs: Rational) -> Rational {
        if self.denominator == rhs.denominator {
            return Rational {
                numerator: self.numerator + rhs.numerator,
                denominator: self.denominator,
            }
            .simplify();
        }
        // a/b + x/y = ay/by + bx/by = (ay+bx)/by
        Rational {
            numerator: self.numerator * rhs.denominator + self.denominator * rhs.numerator,
            denominator: self.denominator * rhs.denominator,
        }
        .simplify()
    }
}

impl Sub for Rational {
    type Output = Rational;
    fn sub(self, rhs: Rational) -> Rational {
        // TODO Maybe optimise? I'm keeping it simple for now.
        self + (-rhs)
    }
}

impl Mul for Rational {
    type Output = Rational;
    fn mul(self, rhs: Rational) -> Rational {
        Rational {
            numerator: self.numerator * rhs.numerator,
            denominator: self.denominator * rhs.denominator,
        }
        .simplify()
    }
}

impl Div for Rational {
    type Output = Rational;
    fn div(self, rhs: Rational) -> Rational {
        Rational {
            numerator: self.numerator * rhs.denominator,
            denominator: self.denominator * rhs.numerator,
        }
        .simplify()
    }
}

impl Rational {
    pub fn sign_int(&self) -> Int {
        self.numerator.signnum() * self.denominator.signnum()
    }

    pub fn sign_i8(&self) -> i8 {
        self.numerator.sign_i8() * self.denominator.sign_i8()
    }
}

impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        use Int::{Infinity, NegInfinity, I};
        write!(
            f,
            "{}",
            match self {
                Infinity => "Infinity".to_string(),
                NegInfinity => "-Infinity".to_string(),
                I(x) => format!("{}", x),
            }
        )
    }
}

impl fmt::Display for EvalInt {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        write!(f, "{}", self.val)?;
        if self.bit_more {
            write!(f, " + ε")?;
            if self.bit_less {
                write!(f, " - δ")?;
            }
        } else if self.bit_less {
            write!(f, " - ε")?;
        }
        Ok(())
    }
}

impl fmt::Display for Rational {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result<(), fmt::Error> {
        if self.denominator == Int::ONE {
            write!(f, "{}", self.numerator)
        } else {
            write!(f, "{}/{}", self.numerator, self.denominator)
        }
    }
}
