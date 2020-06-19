use std::ops::{Add, BitAnd, BitOr, Mul, Neg};

/// Tracks possible signs
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Sign {
    /// Maybe Positive: 001
    /// Maybe 0:        010
    /// Maybe Negative: 100
    bits: u8,
}

impl Sign {
    pub const POSITIVE: Sign = Sign { bits: 0b001 };
    pub const ZERO: Sign = Sign { bits: 0b010 };
    pub const NEGATIVE: Sign = Sign { bits: 0b100 };
    pub const NON_NEGATIVE: Sign = Sign { bits: 0b011 };
    pub const NON_POSITIVE: Sign = Sign { bits: 0b110 };
    pub const UNKNOWN: Sign = Sign { bits: 0b111 };
    pub const NULL: Sign = Sign { bits: 0 };

    /// Returns true iff self *could* be negative
    pub fn maybe_neg(self) -> bool {
        (self & Sign::NEGATIVE).into()
    }
    /// Returns true iff self *could* be zero
    pub fn maybe_zero(self) -> bool {
        (self & Sign::ZERO).into()
    }
    /// Returns true iff self *could* be positive
    pub fn maybe_pos(self) -> bool {
        (self & Sign::POSITIVE).into()
    }
}

impl BitOr for Sign {
    type Output = Sign;
    fn bitor(self, other: Sign) -> Sign {
        Sign {
            bits: self.bits | other.bits,
        }
    }
}

impl BitAnd for Sign {
    type Output = Sign;
    fn bitand(self, other: Sign) -> Sign {
        Sign {
            bits: self.bits & other.bits,
        }
    }
}

macro_rules! use_sign {
    (NEG, ZERO, POS, NULL) => {
        const NEG: Sign = Sign::NEGATIVE;
        const ZERO: Sign = Sign::ZERO;
        const POS: Sign = Sign::POSITIVE;
        const NULL: Sign = Sign::NULL;
    }
}
macro_rules! use_more_sign {
    (NON_NEG, NON_POS, UNKNOWN) => {
        const NON_NEG: Sign = Sign::NON_NEGATIVE;
        const NON_POS: Sign = Sign::NON_POSITIVE;
        const UNKNOWN: Sign = Sign::UNKNOWN;
    }
}

impl Neg for Sign {
    type Output = Sign;
    fn neg(self) -> Sign {
        use_sign!(NEG, ZERO, POS, NULL);
        (if self.maybe_zero() { ZERO } else { NULL }
            | if self.maybe_pos() { NEG } else { NULL }
            | if self.maybe_neg() { POS } else { NULL })
    }
}


impl Mul for Sign {
    type Output = Sign;
    fn mul(self, other: Sign) -> Sign {
        use_sign!(NEG, ZERO, POS, NULL);
        (if self.maybe_zero() || other.maybe_zero() { ZERO } else { NULL }
            | if self.maybe_pos() && other.maybe_pos()
                 || self.maybe_neg() && other.maybe_neg() { POS } else { NULL }
            | if self.maybe_pos() && other.maybe_neg()
                 || self.maybe_neg() && other.maybe_pos() { NEG } else { NULL })
    }
}

impl Add for Sign {
    type Output = Sign;
    fn add(self, other: Sign) -> Sign {
        use_sign!(NEG, ZERO, POS, NULL);
        use_more_sign!(NON_NEG, NON_POS, UNKNOWN);
        match (self, other) {
            (UNKNOWN, _) => UNKNOWN,
            (_, UNKNOWN) => UNKNOWN,
            (s, ZERO) => s,
            (ZERO, s) => s,
            (POS, POS) => POS,
            (POS, NON_NEG) => POS,
            (NON_NEG, POS) => POS,
            (NON_NEG, NON_NEG) => NON_NEG,
            (NEG, NEG) => NEG,
            (NEG, NON_POS) => NEG,
            (NON_POS, NEG) => NEG,
            (NON_POS, NON_POS) => NON_POS,
            (POS, NEG) => UNKNOWN,
            (NEG, POS) => UNKNOWN,
            (NON_NEG, NON_POS) => UNKNOWN,
            (NON_POS, NON_NEG) => UNKNOWN,
            (POS, NON_POS) => UNKNOWN,
            (NON_POS, POS) => UNKNOWN,
            (NEG, NON_NEG) => UNKNOWN,
            (NON_NEG, NEG) => UNKNOWN,
            _ => panic!("unexpected sign combination"),
        }
    }
}

impl From<Sign> for bool {
    fn from(sign: Sign) -> bool {
        sign.bits != 0
    }
}
