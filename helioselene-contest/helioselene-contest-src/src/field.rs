use core::{
    convert::{Into, TryInto},
    iter::{Product, Sum},
    ops::{Add, AddAssign, DerefMut, Mul, MulAssign, Neg, Sub, SubAssign},
};

use crypto_bigint::{Encoding, U256};
use ff::{helpers::sqrt_ratio_generic, Field, FieldBits, PrimeField, PrimeFieldBits};
use rand_core::RngCore;
use subtle::{Choice, ConditionallySelectable, ConstantTimeEq, CtOption};
use zeroize::{DefaultIsZeroes, Zeroize};

use crate::u8_from_bool;

const LIMBS: usize = 4;

const MODULUS: [u64; LIMBS] = [
    7977795179034167199,
    13798879916737260376,
    18446744073709551615,
    9223372036854775807,
];

const MODULUS_PLUS_ONE_DIV_FOUR: [u64; LIMBS] = [
    1994448794758541800,
    17284778034466478806,
    18446744073709551615,
    2305843009213693951,
];

const C: [u64; 2] = [10468948894675384417, 4647864156972291239]; // 127 bit

// C*2
const TWO_C: [u64; 2] = [2491153715641217218, 9295728313944582479]; // 128 bit

#[derive(Clone, Copy, Default, Debug)]
pub struct HelioseleneField(pub [u64; LIMBS]);

impl DefaultIsZeroes for HelioseleneField {}

macro_rules! math_op {
    (
    $Value: ident,
    $Other: ident,
    $Op: ident,
    $op_fn: ident,
    $Assign: ident,
    $assign_fn: ident,
    $function: expr
  ) => {
        impl $Op<$Other> for $Value {
            type Output = $Value;
            fn $op_fn(self, other: $Other) -> Self::Output {
                $function(&self, &other)
            }
        }
        impl $Assign<$Other> for $Value {
            fn $assign_fn(&mut self, other: $Other) {
                *self = $function(&self, &other);
            }
        }
        impl<'a> $Op<&'a $Other> for $Value {
            type Output = $Value;
            fn $op_fn(self, other: &'a $Other) -> Self::Output {
                $function(&self, other)
            }
        }
        impl<'a> $Assign<&'a $Other> for $Value {
            fn $assign_fn(&mut self, other: &'a $Other) {
                *self = $function(&self, other);
            }
        }
    };
}

math_op!(
    HelioseleneField,
    HelioseleneField,
    Add,
    add,
    AddAssign,
    add_assign,
    HelioseleneField::add_inner
);
math_op!(
    HelioseleneField,
    HelioseleneField,
    Sub,
    sub,
    SubAssign,
    sub_assign,
    HelioseleneField::sub_inner
);
math_op!(
    HelioseleneField,
    HelioseleneField,
    Mul,
    mul,
    MulAssign,
    mul_assign,
    HelioseleneField::mul_inner
);

impl Neg for HelioseleneField {
    type Output = HelioseleneField;

    fn neg(self) -> Self::Output {
        HelioseleneField::ZERO.sub_inner(&self)
    }
}

impl<'a> Neg for &'a HelioseleneField {
    type Output = HelioseleneField;

    fn neg(self) -> Self::Output {
        HelioseleneField::ZERO.sub_inner(self)
    }
}

impl PartialEq<Self> for HelioseleneField {
    fn eq(&self, other: &Self) -> bool {
        self.to_bytes() == other.to_bytes()
    }
}

impl Eq for HelioseleneField {}

impl Field for HelioseleneField {
    const ZERO: Self = Self([0, 0, 0, 0]);
    const ONE: Self = Self([1, 0, 0, 0]);

    fn random(mut rng: impl RngCore) -> Self {
        let mut bytes = [0; 64];
        rng.fill_bytes(&mut bytes);
        Self::wide_reduce(bytes)
    }

    fn square(&self) -> Self {
        let res = square_l(&self.0);

        Self::wide_reduce_limbs(res)
    }

    fn double(&self) -> Self {
        let mut res = [0; LIMBS];

        res[0] = self.0[0] << 1;
        (res[1], _) = add2(self.0[1] << 1, self.0[0] >> 63);
        (res[2], _) = add2(self.0[2] << 1, self.0[1] >> 63);
        (res[3], _) = add2(self.0[3] << 1, self.0[2] >> 63);

        let overflow = self.0[3] >> 63;
        let c = [TWO_C[0] * overflow, TWO_C[1] * overflow];
        let (res, overflow) = add_l_r_2(&res, &c);

        let c = [TWO_C[0] * overflow, TWO_C[1] * overflow];
        let (res, _) = add_l_r_2(&res, &c);

        Self(res)
    }

    fn invert(&self) -> CtOption<Self> {
        let res = self.pow_vartime(Self::NEG_TWO);
        CtOption::new(res, res.0.ct_ne(&[0; 4]))
    }

    fn sqrt(&self) -> CtOption<Self> {
        let res = self.pow_vartime(HelioseleneField(MODULUS_PLUS_ONE_DIV_FOUR));
        CtOption::new(res, res.square().to_bytes().ct_eq(&self.to_bytes()))
    }

    fn sqrt_ratio(num: &Self, div: &Self) -> (Choice, Self) {
        sqrt_ratio_generic(num, div)
    }
}

impl PrimeField for HelioseleneField {
    type Repr = [u8; 32];

    fn from_repr(bytes: Self::Repr) -> CtOption<Self> {
        let limbs = [
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
        ];

        let res = Self(limbs);

        CtOption::new(res, res.to_bytes().ct_eq(&bytes))
    }

    fn to_repr(&self) -> Self::Repr {
        self.to_bytes()
    }
    fn is_odd(&self) -> Choice {
        Choice::from(self.to_bytes()[0] & 0b1)
    }

    const MODULUS: &'static str =
        "7fffffffffffffffffffffffffffffffbf7f782cb7656b586eb6d2727927c79f";

    const NUM_BITS: u32 = 255;
    const CAPACITY: u32 = 254;

    const TWO_INV: Self = Self([
        3988897589517083600,
        16122811995223405996,
        18446744073709551615,
        4611686018427387903,
    ]);

    const MULTIPLICATIVE_GENERATOR: Self = Self([5, 0, 0, 0]);

    const S: u32 = 1;

    const ROOT_OF_UNITY: Self = Self([
        7977795179034167198,
        13798879916737260376,
        18446744073709551615,
        9223372036854775807,
    ]);
    const ROOT_OF_UNITY_INV: Self = Self([
        7977795179034167198,
        13798879916737260376,
        18446744073709551615,
        9223372036854775807,
    ]);

    const DELTA: Self = Self([25, 0, 0, 0]);
}

impl PrimeFieldBits for HelioseleneField {
    type ReprBits = [u8; 32];

    fn to_le_bits(&self) -> FieldBits<Self::ReprBits> {
        self.to_repr().into()
    }

    fn char_le_bits() -> FieldBits<Self::ReprBits> {
        U256::from_be_hex(Self::MODULUS).to_le_bytes().into()
    }
}

impl ConditionallySelectable for HelioseleneField {
    fn conditional_select(a: &Self, b: &Self, choice: Choice) -> Self {
        Self([
            u64::conditional_select(&a.0[0], &b.0[0], choice),
            u64::conditional_select(&a.0[1], &b.0[1], choice),
            u64::conditional_select(&a.0[2], &b.0[2], choice),
            u64::conditional_select(&a.0[3], &b.0[3], choice),
        ])
    }
}

impl ConstantTimeEq for HelioseleneField {
    fn ct_eq(&self, other: &Self) -> Choice {
        self.to_bytes().ct_eq(&other.to_bytes())
    }
}

impl HelioseleneField {
    const NEG_TWO: Self = Self([7977795179034167197, 13798879916737260376, 18446744073709551615, 9223372036854775807]);

    pub fn pow(&self, other: HelioseleneField) -> HelioseleneField {
        let mut table = [Self::ONE; 16];
        table[1] = *self;
        for i in 2..16 {
            table[i] = table[i - 1].mul_inner(&self);
        }

        let mut res = Self::ONE;
        let mut bits = 0;
        for (i, mut bit) in other.to_le_bits().iter_mut().rev().enumerate() {
            bits <<= 1;
            let mut bit = u8_from_bool(bit.deref_mut());
            bits |= bit;
            bit.zeroize();

            if ((i + 1) % 4) == 0 {
                if i != 3 {
                    for _ in 0..4 {
                        res = res.square();
                    }
                }

                let mut factor = table[0];
                for (j, candidate) in table[1..].iter().enumerate() {
                    let j = j + 1;
                    factor =
                        Self::conditional_select(&factor, &candidate, usize::from(bits).ct_eq(&j));
                }
                res = res.mul_inner(&factor);
                bits = 0;
            }
        }
        res
    }

    /// Exponentiation which executes in variable time with different exponents.
    ///
    /// Given the same exponent this should execute in constant time.
    fn pow_vartime(&self, other: HelioseleneField) -> HelioseleneField {
        let mut table = [Self::ONE; 16];
        table[1] = *self;
        for i in 2..16 {
            table[i] = table[i - 1].mul_inner(&self);
        }

        let mut res = Self::ONE;

        for (i, limb) in other.0.into_iter().rev().enumerate() {
            let mut j = 64;
            while j != 0 {
                j -= 4;

                if i != 0 || j != 64 {
                    for _ in 0..4 {
                        res = res.square();
                    }
                }

                let bits = limb >> j & 0b1111;

                if bits != 0 {
                    res = res.mul_inner(&table[bits as usize]);
                }
            }
        }
        res
    }

    fn mul_inner(&self, rhs: &HelioseleneField) -> HelioseleneField {
        let res = mul_l_r(&self.0, &rhs.0);

        Self::wide_reduce_limbs(res)
    }

    fn to_bytes(self) -> [u8; 32] {
        let mut limbs = self.0;
        // Take the extra bit off of limbs.
        let extra_bit = limbs[LIMBS - 1] >> 63;
        limbs[LIMBS - 1] &= !(1 << 63);

        // Add: lo + C?
        // lo: 255 bit
        // C: 127 bit
        // 256 bit output
        let c = [C[0] * extra_bit, C[1] * extra_bit];
        let (mut limbs, _) = add_l_r_2(&limbs, &c);

        // if lo was more than 2^255 - C? - 1, then lo would have overflowed into the 256 bit. With the wrapping
        // bits max value being C - 1.
        // if lo did not overflow then it is 255 bits and successfully reduced, the next step will be a no-op.
        // if lo did overflow then repeating this again will clear the high bit and reduce.

        let extra_bit = limbs[LIMBS - 1] >> 63;
        limbs[LIMBS - 1] &= !(1 << 63);

        let c = [C[0] * extra_bit, C[1] * extra_bit];
        let (res, _) = add_l_r_2(&limbs, &c);

        let (res2, overflow) = sub_l_r_4(&res, &MODULUS);

        let choice = Choice::from(overflow as u8);

        let mut ret = [0; 32];

        ret[0..8]
            .copy_from_slice(&u64::conditional_select(&res2[0], &res[0], choice).to_le_bytes());
        ret[8..16]
            .copy_from_slice(&u64::conditional_select(&res2[1], &res[1], choice).to_le_bytes());
        ret[16..24]
            .copy_from_slice(&u64::conditional_select(&res2[2], &res[2], choice).to_le_bytes());
        ret[24..32]
            .copy_from_slice(&u64::conditional_select(&res2[3], &res[3], choice).to_le_bytes());

        ret
    }

    const fn sub_inner(&self, rhs: &HelioseleneField) -> HelioseleneField {
        let (res, overflow) = sub_l_r_4(&self.0, &rhs.0);

        let c = [TWO_C[0] * overflow, TWO_C[1] * overflow];

        let (res, overflow) = sub_l_r_2(&res, &c);

        let c = [TWO_C[0] * overflow, TWO_C[1] * overflow];

        let (res, _) = sub_l_r_2(&res, &c);

        Self(res)
    }

    #[inline(always)]
    const fn add_inner(&self, rhs: &HelioseleneField) -> HelioseleneField {
        let (res, overflow) = add_l_r_4(&self.0, &rhs.0);

        let c = [TWO_C[0] * overflow, TWO_C[1] * overflow];
        let (res, overflow) = add_l_r_2(&res, &c);

        let c = [TWO_C[0] * overflow, TWO_C[1] * overflow];
        let (res, _) = add_l_r_2(&res, &c);

        Self(res)
    }

    fn wide_reduce(bytes: [u8; 64]) -> HelioseleneField {
        let limbs = [
            u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
            u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
            u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
            u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
            u64::from_le_bytes(bytes[32..40].try_into().unwrap()),
            u64::from_le_bytes(bytes[40..48].try_into().unwrap()),
            u64::from_le_bytes(bytes[48..56].try_into().unwrap()),
            u64::from_le_bytes(bytes[56..64].try_into().unwrap()),
        ];

        Self::wide_reduce_limbs(limbs)
    }

    fn wide_reduce_limbs(limbs: [u64; LIMBS * 2]) -> HelioseleneField {
        // Crandalls reduction algorithm.
        // Output will take up the full 256 bits as this is only a partial reduction.
        // Idea from: <https://github.com/iri031/constantine/blob/585f803b9444b1d021c1e2da0857c088f0bf410f/constantine/math/arithmetic/limbs_crandall.nim#L51>

        // Split lo & hi bits at WORDS.
        let lo: &[u64; LIMBS] = (&limbs[..LIMBS]).try_into().unwrap();

        // We don't take the high bit off of lo as this is only a partial reduction.

        // Multiply hi by 2C.
        let hi_mul_C = mul_C_4((&limbs[LIMBS..]).try_into().unwrap());

        // Add: lo + hi*2C?
        // lo: 255 bit.
        // hi*2C: 384 bit.
        // 385 bit output
        let (limbs, carry) = add_l_r_6_2(&hi_mul_C, lo);

        // Split lo & hi bits at WORDS.
        let mut lo: [u64; LIMBS] = limbs[..LIMBS].try_into().unwrap();

        // Take the extra bit off of lo.
        // We take the high bit here as we can easily add it onto the next addition.
        let extra_bit = lo[LIMBS - 1] >> 63;
        lo[LIMBS - 1] &= !(1 << 63);

        // Multiply hi by 2C.
        let hi_mul_C = mul_C_2((&limbs[LIMBS..]).try_into().unwrap());

        // Add: lo + hi*2C + 2C*2^128? + C?
        // lo: 255 bit.
        // hi*2C: 256 bit
        // 2C^128 + C: 256 bit
        // 258 bit output
        let c_2c = [
            C[0] * extra_bit,
            C[1] * extra_bit,
            TWO_C[0] * carry,
            TWO_C[1] * carry,
        ];
        let (lo, carry1) = add_l_r_4(&hi_mul_C, &lo);
        let (mut lo, carry2) = add_l_r_4(&lo, &c_2c);
        let c2_mul = carry1 + carry2;

        // Take the extra bit off of lo.
        let extra_bit = lo[LIMBS - 1] >> 63;
        lo[LIMBS - 1] &= !(1 << 63);

        // Add: lo + 2C*2? + C?
        // lo: 255 bit
        // 2C*2? + C: 129 bits
        // 256 bit output
        let (top, overflow) = TWO_C[1].overflowing_mul(c2_mul);
        let c = [
            C[0] * extra_bit + TWO_C[0] * c2_mul, // can't overflow.
            C[1] * extra_bit + top,
            overflow as u64,
        ];
        let (res, _) = add_l_r_3(&lo, &c);

        // We keep the last bit as unreduced.

        HelioseleneField(res)
    }
}

#[inline(always)]
fn square_l(l: &[u64; 4]) -> [u64; 8] {
    let mut res = [0; 8];

    let mut i = 1;
    while i < 4 {
        let mut carry = 0;
        let mut j = 0;
        while j < i {
            (carry, res[i + j]) = mul_add2(l[i], l[j], res[i + j], carry);
            j += 1;
        }
        res[i + j] = carry;
        i += 1;
    }

    let mut carry = 0;
    let mut i = 0;
    while i < 8 {
        (carry, res[i]) = (res[i] >> 63, (res[i] << 1) + carry);
        i += 1;
    }

    let mut i = 0;
    let mut carry = 0;
    while i < 4 {
        (carry, res[i + i]) = mul_add2(l[i], l[i], res[i + i], carry);
        (res[i + i + 1], carry) = add2(carry, res[i + i + 1]);
        i += 1;
    }

    res
}

#[inline(always)]
fn mul_l_r(l: &[u64; 4], r: &[u64; 4]) -> [u64; 8] {
    let mut res = [0; 8];

    let mut hi;
    let mut i = 0;
    while i < 4 {
        (hi, res[i]) = mul_add(l[i], r[0], res[i]);

        (hi, res[i + 1]) = mul_add2(l[i], r[1], hi, res[i + 1]);

        (hi, res[i + 2]) = mul_add2(l[i], r[2], hi, res[i + 2]);

        (res[i + 4], res[i + 3]) = mul_add2(l[i], r[3], hi, res[i + 3]);

        i += 1;
    }

    res
}

#[inline(always)]
const fn sub_l_r_4(l: &[u64; 4], r: &[u64; 4]) -> ([u64; 4], u64) {
    let mut res = [0; 4];
    let mut carry;

    (res[0], carry) = sub2(l[0], r[0]);
    (res[1], carry) = sub3(l[1], r[1], carry);
    (res[2], carry) = sub3(l[2], r[2], carry);
    (res[3], carry) = sub3(l[3], r[3], carry);

    (res, carry)
}

#[inline(always)]
const fn sub_l_r_2(b: &[u64; 4], s: &[u64; 2]) -> ([u64; 4], u64) {
    let mut res = [0; LIMBS];
    let mut carry;

    (res[0], carry) = sub2(b[0], s[0]);
    (res[1], carry) = sub3(b[1], s[1], carry);
    (res[2], carry) = sub2(b[2], carry);
    (res[3], carry) = sub2(b[3], carry);

    (res, carry)
}

#[inline(always)]
const fn sub2(l: u64, r: u64) -> (u64, u64) {
    let l = l as u128;
    let r = r as u128;
    let res = l.wrapping_sub(r);
    (res as u64, (res >> 127) as u64)
}

#[inline(always)]
const fn sub3(l: u64, r: u64, c: u64) -> (u64, u64) {
    let l = l as u128;
    let r = r as u128;
    let c = c as u128;
    let res = l.wrapping_sub(r + c);
    (res as u64, (res >> 127) as u64)
}

#[inline(always)]
const fn add_l_r_4(l: &[u64; 4], r: &[u64; 4]) -> ([u64; 4], u64) {
    let mut res = [0; 4];

    let mut carry;
    (res[0], carry) = add2(l[0], r[0]);
    (res[1], carry) = add3(l[1], r[1], carry);
    (res[2], carry) = add3(l[2], r[2], carry);
    (res[3], carry) = add3(l[3], r[3], carry);

    (res, carry)
}

#[inline(always)]
const fn add_l_r_2(l: &[u64; 4], r: &[u64; 2]) -> ([u64; 4], u64) {
    let mut res = [0; 4];

    let mut carry;
    (res[0], carry) = add2(l[0], r[0]);
    (res[1], carry) = add3(l[1], r[1], carry);
    (res[2], carry) = add2(l[2], carry);
    (res[3], carry) = add2(l[3], carry);

    (res, carry)
}

#[inline(always)]
const fn add_l_r_3(l: &[u64; 4], r: &[u64; 3]) -> ([u64; 4], u64) {
    let mut res = [0; 4];

    let mut carry;
    (res[0], carry) = add2(l[0], r[0]);
    (res[1], carry) = add3(l[1], r[1], carry);
    (res[2], carry) = add3(l[2], r[2], carry);
    (res[3], carry) = add2(l[3], carry);

    (res, carry)
}

#[inline(always)]
const fn add_l_r_6_2(l: &[u64; 6], r: &[u64; 4]) -> ([u64; 6], u64) {
    let mut res = [0; 6];

    let mut carry;
    (res[0], carry) = add2(l[0], r[0]);
    (res[1], carry) = add3(l[1], r[1], carry);
    (res[2], carry) = add3(l[2], r[2], carry);
    (res[3], carry) = add3(l[3], r[3], carry);
    (res[4], carry) = add2(l[4], carry);
    (res[5], carry) = add2(l[5], carry);

    (res, carry)
}

#[inline(always)]
const fn add2(l: u64, r: u64) -> (u64, u64) {
    let l = l as u128;
    let r = r as u128;
    let res = l + r;
    (res as u64, (res >> 64) as u64)
}

#[inline(always)]
const fn add3(l: u64, r: u64, c: u64) -> (u64, u64) {
    let l = l as u128;
    let r = r as u128;
    let c = c as u128;
    let res = l + r + c;
    (res as u64, (res >> 64) as u64)
}

#[inline(always)]
const fn add4(l: u64, r: u64, c: u64, cc: u64) -> (u64, u64) {
    let l = l as u128;
    let r = r as u128;
    let c = c as u128;
    let cc = cc as u128;
    let res = l + r + c + cc;
    (res as u64, (res >> 64) as u64)
}

#[inline(always)]
const fn add5(l: u64, r: u64, c: u64, cc: u64, ccc: u64) -> (u64, u64) {
    let l = l as u128;
    let r = r as u128;
    let c = c as u128;
    let cc = cc as u128;
    let ccc = ccc as u128;
    let res = l + r + c + cc + ccc;
    (res as u64, (res >> 64) as u64)
}

#[inline(always)]
#[allow(non_snake_case)]
fn mul_C_4(l: &[u64; 4]) -> [u64; 6] {
    let (md12, lo1) = mul(l[0], TWO_C[0]);
    let (md13, lo2) = mul(l[1], TWO_C[0]);
    let (md14, lo3) = mul(l[2], TWO_C[0]);
    let (md15, lo4) = mul(l[3], TWO_C[0]);

    let (hi3, md22) = mul(l[0], TWO_C[1]);
    let (hi4, md23) = mul(l[1], TWO_C[1]);
    let (hi5, md24) = mul(l[2], TWO_C[1]);
    let (hi6, md25) = mul(l[3], TWO_C[1]);

    let mut res = [0; 6];

    let mut carry;
    res[0] = lo1;
    (res[1], carry) = add3(lo2, md12, md22);
    (res[2], carry) = add5(hi3, lo3, md13, md23, carry);
    (res[3], carry) = add5(hi4, lo4, md14, md24, carry);
    (res[4], carry) = add4(hi5, md15, md25, carry);
    (res[5], _) = add2(carry, hi6);

    res
}

#[inline(always)]
#[allow(non_snake_case)]
fn mul_C_2(l: &[u64; 2]) -> [u64; 4] {
    let (md12, lo1) = mul(l[0], TWO_C[0]);
    let (md13, lo2) = mul(l[1], TWO_C[0]);

    let (hi3, md22) = mul(l[0], TWO_C[1]);
    let (hi4, md23) = mul(l[1], TWO_C[1]);

    let mut res = [0; 4];

    let mut carry;
    res[0] = lo1;
    (res[1], carry) = add3(lo2, md12, md22);
    (res[2], carry) = add4(hi3, md13, md23, carry);
    (res[3], _) = add2(hi4, carry);

    res
}

#[inline(always)]
fn mul(l: u64, r: u64) -> (u64, u64) {
    let res = l as u128 * r as u128;
    ((res >> 64) as u64, res as u64)
}

#[inline(always)]
fn mul_add(l: u64, r: u64, c: u64) -> (u64, u64) {
    let res = l as u128 * r as u128 + c as u128;
    ((res >> 64) as u64, res as u64)
}

#[inline(always)]
fn mul_add2(l: u64, r: u64, c1: u64, c2: u64) -> (u64, u64) {
    let res = l as u128 * r as u128 + c1 as u128 + c2 as u128;
    ((res >> 64) as u64, res as u64)
}

impl<T: Into<u64>> From<T> for HelioseleneField {
    fn from(x: T) -> Self {
        Self([x.into(), 0, 0, 0])
    }
}

impl Sum<HelioseleneField> for HelioseleneField {
    fn sum<I: Iterator<Item = HelioseleneField>>(iter: I) -> HelioseleneField {
        let mut res = HelioseleneField::ZERO;
        for item in iter {
            res += item;
        }
        res
    }
}

impl<'a> Sum<&'a HelioseleneField> for HelioseleneField {
    fn sum<I: Iterator<Item = &'a HelioseleneField>>(iter: I) -> HelioseleneField {
        iter.cloned().sum()
    }
}

impl Product<HelioseleneField> for HelioseleneField {
    fn product<I: Iterator<Item = HelioseleneField>>(iter: I) -> HelioseleneField {
        let mut res = HelioseleneField::ONE;
        for item in iter {
            res *= item;
        }
        res
    }
}

impl<'a> Product<&'a HelioseleneField> for HelioseleneField {
    fn product<I: Iterator<Item = &'a HelioseleneField>>(iter: I) -> HelioseleneField {
        iter.cloned().product()
    }
}

#[test]
fn test_helioselene_field() {
  ff_group_tests::prime_field::test_prime_field_bits::<_, HelioseleneField>(&mut rand_core::OsRng);
}
