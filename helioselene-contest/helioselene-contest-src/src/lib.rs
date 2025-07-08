#![cfg_attr(docsrs, feature(doc_auto_cfg))]
#![doc = include_str!("../README.md")]
#![no_std]
#![allow(non_snake_case)]

extern crate alloc;

pub use group;

pub use dalek_ff_group::FieldElement as Field25519;

mod field;
pub use field::HelioseleneField;

mod point;
pub use point::{HeliosPoint, SelenePoint};

// Use black_box when possible
#[rustversion::since(1.66)]
use core::hint::black_box;
#[rustversion::before(1.66)]
fn black_box<T>(val: T) -> T {
    val
}

pub(crate) fn u8_from_bool(bit_ref: &mut bool) -> u8 {
    use zeroize::Zeroize;

    let bit_ref = black_box(bit_ref);

    let mut bit = black_box(*bit_ref);
    let res = black_box(bit as u8);
    bit.zeroize();
    debug_assert!((res | 1) == 1);

    bit_ref.zeroize();
    res
}