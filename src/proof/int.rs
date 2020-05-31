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

impl Int {
    pub const ZERO: Int = Int::I(0);
    pub const ONE: Int = Int::I(1);

    pub fn is_finite(&self) -> bool {
        use Int::{Infinity, NegInfinity, I};
        match self {
            I(_) => true,
            Infinity | NegInfinity => false,
        }
    }
}

impl<T: Into<i128>> From<T> for Int {
    fn from(x: T) -> Int {
        Int::I(x.into())
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
    /// Integer division. The result is floored.
    fn div(self, rhs: Int) -> Int {
        use Int::{Infinity, NegInfinity, I};
        match (&self, &rhs) {
            (_, I(0)) => panic!("divide by 0"),

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
        (self / rhs)
            + if self % rhs == Int::ZERO {
                Int::ZERO
            } else {
                Int::ONE
            }
    }

    /// Divide and round down
    pub fn div_floor(self, rhs: Int) -> Int {
        self / rhs
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
