//! SDQL Runtime Library
//!
//! This module provides the core types, traits, and helper functions needed by
//! Lean-generated SDQL Rust code. It includes:
//! - Custom types: Real (Ord-capable f64), Date (YYYYMMDD integer)
//! - Semimodule operations: SdqlAdd trait and implementations
//! - Dictionary/tuple helpers: dict_add, tuple_addN, lookup_or_default
//! - Extension functions: ext_and, ext_or, ext_eq, ext_leq, ext_sub, etc.
//! - TBL file loading: load_tbl, build_col, FromTblField trait
//! - Pretty-printing: SDQLShow trait and implementations

use std::collections::BTreeMap;
use std::ops::{Add, Mul, Sub};
use std::cmp::Ordering;
use std::io::{BufRead, BufReader};
use std::fs::File;

// ============================================================================
// Core Types
// ============================================================================

/// Ord-capable f64 wrapper for SDQL real type.
/// Provides total ordering by treating NaN consistently.
#[derive(Debug, Clone, Copy, Default)]
pub struct Real(pub f64);

impl Real {
    pub fn new(v: f64) -> Self { Real(v) }
}

impl PartialEq for Real {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0 || (self.0.is_nan() && other.0.is_nan())
    }
}

impl Eq for Real {}

impl PartialOrd for Real {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for Real {
    fn cmp(&self, other: &Self) -> Ordering {
        self.0.partial_cmp(&other.0).unwrap_or_else(|| {
            if self.0.is_nan() && other.0.is_nan() { Ordering::Equal }
            else if self.0.is_nan() { Ordering::Greater }
            else { Ordering::Less }
        })
    }
}

impl Add for Real {
    type Output = Self;
    fn add(self, rhs: Self) -> Self { Real(self.0 + rhs.0) }
}

impl Sub for Real {
    type Output = Self;
    fn sub(self, rhs: Self) -> Self { Real(self.0 - rhs.0) }
}

impl Mul for Real {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self { Real(self.0 * rhs.0) }
}

/// SDQL max-product semiring scalar type.
///
/// Underlying carrier is `Real`, but addition is `max` (not `+`).
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord)]
pub struct MaxProduct(pub Real);

impl Mul for MaxProduct {
    type Output = Self;
    fn mul(self, rhs: Self) -> Self { MaxProduct(self.0 * rhs.0) }
}

/// SDQL Date type: stored as YYYYMMDD integer for ordering.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Default, Hash)]
pub struct Date(pub i64);

impl Date {
    pub fn new(yyyymmdd: i64) -> Self { Date(yyyymmdd) }
}

impl Add for Date {
    type Output = Self;
    fn add(self, rhs: Self) -> Self { rhs }
}

/// Macro for creating Date literals.
#[macro_export]
macro_rules! date {
    ($yyyymmdd:literal) => {{ Date::new($yyyymmdd) }};
}

// ============================================================================
// Semimodule Operations (SdqlAdd)
// ============================================================================

/// Trait for SDQL's additive structure.
/// - bool: OR
/// - numeric types: standard addition
/// - Date: takes rhs (overwrite semantics)
/// - String: concatenation
/// - BTreeMap: pointwise merge with value addition
/// - tuples: componentwise addition
pub trait SdqlAdd {
    fn sdql_add(&self, other: &Self) -> Self;
}

impl SdqlAdd for bool {
    fn sdql_add(&self, other: &Self) -> Self { *self || *other }
}

impl SdqlAdd for i64 {
    fn sdql_add(&self, other: &Self) -> Self { *self + *other }
}

impl SdqlAdd for Real {
    fn sdql_add(&self, other: &Self) -> Self { Real(self.0 + other.0) }
}

impl SdqlAdd for MaxProduct {
    fn sdql_add(&self, other: &Self) -> Self { std::cmp::max(*self, *other) }
}

impl SdqlAdd for Date {
    fn sdql_add(&self, other: &Self) -> Self { *other }
}

impl SdqlAdd for String {
    fn sdql_add(&self, other: &Self) -> Self {
        let mut s = self.clone();
        s.push_str(other);
        s
    }
}

impl<K: Ord + Clone, V: SdqlAdd + Clone> SdqlAdd for BTreeMap<K, V> {
    fn sdql_add(&self, other: &Self) -> Self {
        dict_add(self.clone(), other.clone())
    }
}

// Tuple implementations for arities 1-8
impl<T1: SdqlAdd> SdqlAdd for (T1,) {
    fn sdql_add(&self, other: &Self) -> Self {
        (self.0.sdql_add(&other.0),)
    }
}

impl<T1: SdqlAdd, T2: SdqlAdd> SdqlAdd for (T1, T2) {
    fn sdql_add(&self, other: &Self) -> Self {
        (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1))
    }
}

impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd> SdqlAdd for (T1, T2, T3) {
    fn sdql_add(&self, other: &Self) -> Self {
        (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2))
    }
}

impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd> SdqlAdd for (T1, T2, T3, T4) {
    fn sdql_add(&self, other: &Self) -> Self {
        (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3))
    }
}

impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5) {
    fn sdql_add(&self, other: &Self) -> Self {
        (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4))
    }
}

impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd, T6: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5, T6) {
    fn sdql_add(&self, other: &Self) -> Self {
        (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4), self.5.sdql_add(&other.5))
    }
}

impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd, T6: SdqlAdd, T7: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5, T6, T7) {
    fn sdql_add(&self, other: &Self) -> Self {
        (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4), self.5.sdql_add(&other.5), self.6.sdql_add(&other.6))
    }
}

impl<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd, T6: SdqlAdd, T7: SdqlAdd, T8: SdqlAdd> SdqlAdd for (T1, T2, T3, T4, T5, T6, T7, T8) {
    fn sdql_add(&self, other: &Self) -> Self {
        (self.0.sdql_add(&other.0), self.1.sdql_add(&other.1), self.2.sdql_add(&other.2), self.3.sdql_add(&other.3), self.4.sdql_add(&other.4), self.5.sdql_add(&other.5), self.6.sdql_add(&other.6), self.7.sdql_add(&other.7))
    }
}

// ============================================================================
// Tensor Semiring Helpers (decompose/mkTensor/bilinear)
// ============================================================================

/// Additive identity for SDQL values.
pub trait SdqlZero {
    fn sdql_zero() -> Self;
}

/// Multiplicative identity for scalar types.
pub trait SdqlOne {
    fn sdql_one() -> Self;
}

/// Scalar action on SDQL values.
pub trait SdqlScale<S> {
    fn sdql_scale(s: &S, v: &Self) -> Self;
}

/// Bilinear form on SDQL semimodule values.
pub trait SdqlBilinear {
    type Scalar: SdqlAdd + SdqlZero;
    fn sdql_bilinear(a: &Self, b: &Self) -> Self::Scalar;
}

/// Tensor construction/decomposition driven by the left type.
pub trait TensorLeft<R>: Sized {
    type Tensor;
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor;
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)>;
}

/// Semiring multiplication for tensor types.
pub trait SdqlSemiringTensor<V>: Sized {
    type Scalar: SdqlAdd + SdqlZero + SdqlOne;
    fn decompose(&self) -> Vec<(V, V)>;
    fn mk_tensor(a: &V, b: &V) -> Self;
    fn bilinear(a: &V, b: &V) -> Self::Scalar;
    fn scale(s: &Self::Scalar, t: &Self) -> Self;
    fn zero() -> Self;
    fn add(a: &Self, b: &Self) -> Self;
}

impl SdqlZero for bool {
    fn sdql_zero() -> Self { false }
}

impl SdqlZero for i64 {
    fn sdql_zero() -> Self { 0 }
}

impl SdqlZero for Real {
    fn sdql_zero() -> Self { Real::new(0.0) }
}

impl SdqlZero for MaxProduct {
    fn sdql_zero() -> Self { MaxProduct(Real::new(0.0)) }
}

impl SdqlZero for Date {
    fn sdql_zero() -> Self { Date::new(10101) }
}

impl SdqlZero for String {
    fn sdql_zero() -> Self { String::new() }
}

impl SdqlZero for () {
    fn sdql_zero() -> Self { () }
}

impl<K: Ord, V> SdqlZero for BTreeMap<K, V> {
    fn sdql_zero() -> Self { BTreeMap::new() }
}

macro_rules! impl_sdql_zero_tuple {
    ( $( $T:ident ),+ ) => {
        impl< $( $T: SdqlZero ),+ > SdqlZero for ( $( $T, )+ ) {
            fn sdql_zero() -> Self {
                ( $( $T::sdql_zero(), )+ )
            }
        }
    };
}

impl_sdql_zero_tuple!(T1);
impl_sdql_zero_tuple!(T1, T2);
impl_sdql_zero_tuple!(T1, T2, T3);
impl_sdql_zero_tuple!(T1, T2, T3, T4);
impl_sdql_zero_tuple!(T1, T2, T3, T4, T5);
impl_sdql_zero_tuple!(T1, T2, T3, T4, T5, T6);
impl_sdql_zero_tuple!(T1, T2, T3, T4, T5, T6, T7);
impl_sdql_zero_tuple!(T1, T2, T3, T4, T5, T6, T7, T8);

impl SdqlOne for bool {
    fn sdql_one() -> Self { true }
}

impl SdqlOne for Real {
    fn sdql_one() -> Self { Real::new(1.0) }
}

impl SdqlOne for MaxProduct {
    fn sdql_one() -> Self { MaxProduct(Real::new(1.0)) }
}

impl SdqlScale<bool> for bool {
    fn sdql_scale(s: &bool, v: &Self) -> Self { *s && *v }
}

impl SdqlScale<Real> for Real {
    fn sdql_scale(s: &Real, v: &Self) -> Self { *s * *v }
}

impl SdqlScale<MaxProduct> for MaxProduct {
    fn sdql_scale(s: &MaxProduct, v: &Self) -> Self { *s * *v }
}

impl<S, K: Ord + Clone, V: SdqlScale<S>> SdqlScale<S> for BTreeMap<K, V> {
    fn sdql_scale(s: &S, v: &Self) -> Self {
        let mut out = BTreeMap::new();
        for (k, val) in v.iter() {
            out.insert(k.clone(), V::sdql_scale(s, val));
        }
        out
    }
}

macro_rules! impl_sdql_scale_tuple {
    ( $( $T:ident, $idx:tt ),+ ) => {
        impl<S, $( $T: SdqlScale<S> ),+ > SdqlScale<S> for ( $( $T, )+ ) {
            fn sdql_scale(s: &S, v: &Self) -> Self {
                ( $( $T::sdql_scale(s, &v.$idx), )+ )
            }
        }
    };
}

impl_sdql_scale_tuple!(T1, 0);
impl_sdql_scale_tuple!(T1, 0, T2, 1);
impl_sdql_scale_tuple!(T1, 0, T2, 1, T3, 2);
impl_sdql_scale_tuple!(T1, 0, T2, 1, T3, 2, T4, 3);
impl_sdql_scale_tuple!(T1, 0, T2, 1, T3, 2, T4, 3, T5, 4);
impl_sdql_scale_tuple!(T1, 0, T2, 1, T3, 2, T4, 3, T5, 4, T6, 5);
impl_sdql_scale_tuple!(T1, 0, T2, 1, T3, 2, T4, 3, T5, 4, T6, 5, T7, 6);
impl_sdql_scale_tuple!(T1, 0, T2, 1, T3, 2, T4, 3, T5, 4, T6, 5, T7, 6, T8, 7);

impl SdqlBilinear for bool {
    type Scalar = bool;
    fn sdql_bilinear(a: &Self, b: &Self) -> Self::Scalar { *a && *b }
}

impl SdqlBilinear for Real {
    type Scalar = Real;
    fn sdql_bilinear(a: &Self, b: &Self) -> Self::Scalar { *a * *b }
}

impl SdqlBilinear for MaxProduct {
    type Scalar = MaxProduct;
    fn sdql_bilinear(a: &Self, b: &Self) -> Self::Scalar { *a * *b }
}

impl<K: Ord, V: SdqlBilinear> SdqlBilinear for BTreeMap<K, V>
where
    V::Scalar: SdqlAdd + SdqlZero,
{
    type Scalar = V::Scalar;
    fn sdql_bilinear(a: &Self, b: &Self) -> Self::Scalar {
        let mut acc = V::Scalar::sdql_zero();
        for (k, v1) in a.iter() {
            if let Some(v2) = b.get(k) {
                let term = V::sdql_bilinear(v1, v2);
                acc = acc.sdql_add(&term);
            }
        }
        acc
    }
}

macro_rules! impl_sdql_bilinear_tuple {
    ( $T1:ident, $idx1:tt; $( $T:ident, $idx:tt ),* ) => {
        impl< $T1, $( $T ),* > SdqlBilinear for ( $T1, $( $T, )* )
        where
            $T1: SdqlBilinear,
            $( $T: SdqlBilinear<Scalar = <$T1 as SdqlBilinear>::Scalar>, )*
            <$T1 as SdqlBilinear>::Scalar: SdqlAdd + SdqlZero,
        {
            type Scalar = <$T1 as SdqlBilinear>::Scalar;
            fn sdql_bilinear(a: &Self, b: &Self) -> Self::Scalar {
                let mut acc = <$T1 as SdqlBilinear>::sdql_bilinear(&a.$idx1, &b.$idx1);
                $(
                    let term = <$T as SdqlBilinear>::sdql_bilinear(&a.$idx, &b.$idx);
                    acc = acc.sdql_add(&term);
                )*
                acc
            }
        }
    };
}

impl_sdql_bilinear_tuple!(T1, 0;);
impl_sdql_bilinear_tuple!(T1, 0; T2, 1);
impl_sdql_bilinear_tuple!(T1, 0; T2, 1, T3, 2);
impl_sdql_bilinear_tuple!(T1, 0; T2, 1, T3, 2, T4, 3);
impl_sdql_bilinear_tuple!(T1, 0; T2, 1, T3, 2, T4, 3, T5, 4);
impl_sdql_bilinear_tuple!(T1, 0; T2, 1, T3, 2, T4, 3, T5, 4, T6, 5);
impl_sdql_bilinear_tuple!(T1, 0; T2, 1, T3, 2, T4, 3, T5, 4, T6, 5, T7, 6);
impl_sdql_bilinear_tuple!(T1, 0; T2, 1, T3, 2, T4, 3, T5, 4, T6, 5, T7, 6, T8, 7);

impl<R: SdqlScale<bool> + Clone> TensorLeft<R> for bool {
    type Tensor = R;
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        R::sdql_scale(a, b)
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        vec![(bool::sdql_one(), t.clone())]
    }
}

impl<R: SdqlScale<Real> + Clone> TensorLeft<R> for Real {
    type Tensor = R;
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        R::sdql_scale(a, b)
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        vec![(Real::sdql_one(), t.clone())]
    }
}

impl<R: SdqlScale<MaxProduct> + Clone> TensorLeft<R> for MaxProduct {
    type Tensor = R;
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        R::sdql_scale(a, b)
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        vec![(MaxProduct::sdql_one(), t.clone())]
    }
}

impl<K: Ord + Clone, V: TensorLeft<R>, R: Clone> TensorLeft<R> for BTreeMap<K, V> {
    type Tensor = BTreeMap<K, V::Tensor>;
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        let mut out = BTreeMap::new();
        for (k, v) in a.iter() {
            out.insert(k.clone(), V::mk_tensor_left(v, b));
        }
        out
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        let mut out = Vec::new();
        for (k, v_tensor) in t.iter() {
            for (v_left, r) in V::decompose_tensor(v_tensor) {
                let mut left = BTreeMap::new();
                left.insert(k.clone(), v_left);
                out.push((left, r));
            }
        }
        out
    }
}

impl<R: Clone, A: TensorLeft<R> + SdqlZero> TensorLeft<R> for (A,) {
    type Tensor = (A::Tensor,);
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        (A::mk_tensor_left(&a.0, b),)
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        let mut out = Vec::new();
        for (a_left, r) in A::decompose_tensor(&t.0) {
            out.push(((a_left,), r));
        }
        out
    }
}

impl<R: Clone, A: TensorLeft<R> + SdqlZero, B: TensorLeft<R> + SdqlZero> TensorLeft<R> for (A, B) {
    type Tensor = (A::Tensor, B::Tensor);
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        (A::mk_tensor_left(&a.0, b), B::mk_tensor_left(&a.1, b))
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        let mut out = Vec::new();
        for (a_left, r) in A::decompose_tensor(&t.0) {
            out.push(((a_left, B::sdql_zero()), r));
        }
        for (b_left, r) in B::decompose_tensor(&t.1) {
            out.push(((A::sdql_zero(), b_left), r));
        }
        out
    }
}

impl<R: Clone, A: TensorLeft<R> + SdqlZero, B: TensorLeft<R> + SdqlZero, C: TensorLeft<R> + SdqlZero> TensorLeft<R> for (A, B, C) {
    type Tensor = (A::Tensor, B::Tensor, C::Tensor);
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        (A::mk_tensor_left(&a.0, b), B::mk_tensor_left(&a.1, b), C::mk_tensor_left(&a.2, b))
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        let mut out = Vec::new();
        for (a_left, r) in A::decompose_tensor(&t.0) {
            out.push(((a_left, B::sdql_zero(), C::sdql_zero()), r));
        }
        for (b_left, r) in B::decompose_tensor(&t.1) {
            out.push(((A::sdql_zero(), b_left, C::sdql_zero()), r));
        }
        for (c_left, r) in C::decompose_tensor(&t.2) {
            out.push(((A::sdql_zero(), B::sdql_zero(), c_left), r));
        }
        out
    }
}

impl<R: Clone, A: TensorLeft<R> + SdqlZero, B: TensorLeft<R> + SdqlZero, C: TensorLeft<R> + SdqlZero, D: TensorLeft<R> + SdqlZero> TensorLeft<R> for (A, B, C, D) {
    type Tensor = (A::Tensor, B::Tensor, C::Tensor, D::Tensor);
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        (A::mk_tensor_left(&a.0, b), B::mk_tensor_left(&a.1, b), C::mk_tensor_left(&a.2, b), D::mk_tensor_left(&a.3, b))
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        let mut out = Vec::new();
        for (a_left, r) in A::decompose_tensor(&t.0) {
            out.push(((a_left, B::sdql_zero(), C::sdql_zero(), D::sdql_zero()), r));
        }
        for (b_left, r) in B::decompose_tensor(&t.1) {
            out.push(((A::sdql_zero(), b_left, C::sdql_zero(), D::sdql_zero()), r));
        }
        for (c_left, r) in C::decompose_tensor(&t.2) {
            out.push(((A::sdql_zero(), B::sdql_zero(), c_left, D::sdql_zero()), r));
        }
        for (d_left, r) in D::decompose_tensor(&t.3) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), d_left), r));
        }
        out
    }
}

impl<R: Clone, A: TensorLeft<R> + SdqlZero, B: TensorLeft<R> + SdqlZero, C: TensorLeft<R> + SdqlZero, D: TensorLeft<R> + SdqlZero, E: TensorLeft<R> + SdqlZero> TensorLeft<R> for (A, B, C, D, E) {
    type Tensor = (A::Tensor, B::Tensor, C::Tensor, D::Tensor, E::Tensor);
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        (A::mk_tensor_left(&a.0, b), B::mk_tensor_left(&a.1, b), C::mk_tensor_left(&a.2, b), D::mk_tensor_left(&a.3, b), E::mk_tensor_left(&a.4, b))
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        let mut out = Vec::new();
        for (a_left, r) in A::decompose_tensor(&t.0) {
            out.push(((a_left, B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), E::sdql_zero()), r));
        }
        for (b_left, r) in B::decompose_tensor(&t.1) {
            out.push(((A::sdql_zero(), b_left, C::sdql_zero(), D::sdql_zero(), E::sdql_zero()), r));
        }
        for (c_left, r) in C::decompose_tensor(&t.2) {
            out.push(((A::sdql_zero(), B::sdql_zero(), c_left, D::sdql_zero(), E::sdql_zero()), r));
        }
        for (d_left, r) in D::decompose_tensor(&t.3) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), d_left, E::sdql_zero()), r));
        }
        for (e_left, r) in E::decompose_tensor(&t.4) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), e_left), r));
        }
        out
    }
}

impl<R: Clone, A: TensorLeft<R> + SdqlZero, B: TensorLeft<R> + SdqlZero, C: TensorLeft<R> + SdqlZero, D: TensorLeft<R> + SdqlZero, E: TensorLeft<R> + SdqlZero, F: TensorLeft<R> + SdqlZero> TensorLeft<R> for (A, B, C, D, E, F) {
    type Tensor = (A::Tensor, B::Tensor, C::Tensor, D::Tensor, E::Tensor, F::Tensor);
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        (A::mk_tensor_left(&a.0, b), B::mk_tensor_left(&a.1, b), C::mk_tensor_left(&a.2, b), D::mk_tensor_left(&a.3, b), E::mk_tensor_left(&a.4, b), F::mk_tensor_left(&a.5, b))
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        let mut out = Vec::new();
        for (a_left, r) in A::decompose_tensor(&t.0) {
            out.push(((a_left, B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), F::sdql_zero()), r));
        }
        for (b_left, r) in B::decompose_tensor(&t.1) {
            out.push(((A::sdql_zero(), b_left, C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), F::sdql_zero()), r));
        }
        for (c_left, r) in C::decompose_tensor(&t.2) {
            out.push(((A::sdql_zero(), B::sdql_zero(), c_left, D::sdql_zero(), E::sdql_zero(), F::sdql_zero()), r));
        }
        for (d_left, r) in D::decompose_tensor(&t.3) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), d_left, E::sdql_zero(), F::sdql_zero()), r));
        }
        for (e_left, r) in E::decompose_tensor(&t.4) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), e_left, F::sdql_zero()), r));
        }
        for (f_left, r) in F::decompose_tensor(&t.5) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), f_left), r));
        }
        out
    }
}

impl<R: Clone, A: TensorLeft<R> + SdqlZero, B: TensorLeft<R> + SdqlZero, C: TensorLeft<R> + SdqlZero, D: TensorLeft<R> + SdqlZero, E: TensorLeft<R> + SdqlZero, F: TensorLeft<R> + SdqlZero, G: TensorLeft<R> + SdqlZero> TensorLeft<R> for (A, B, C, D, E, F, G) {
    type Tensor = (A::Tensor, B::Tensor, C::Tensor, D::Tensor, E::Tensor, F::Tensor, G::Tensor);
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        (A::mk_tensor_left(&a.0, b), B::mk_tensor_left(&a.1, b), C::mk_tensor_left(&a.2, b), D::mk_tensor_left(&a.3, b), E::mk_tensor_left(&a.4, b), F::mk_tensor_left(&a.5, b), G::mk_tensor_left(&a.6, b))
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        let mut out = Vec::new();
        for (a_left, r) in A::decompose_tensor(&t.0) {
            out.push(((a_left, B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), F::sdql_zero(), G::sdql_zero()), r));
        }
        for (b_left, r) in B::decompose_tensor(&t.1) {
            out.push(((A::sdql_zero(), b_left, C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), F::sdql_zero(), G::sdql_zero()), r));
        }
        for (c_left, r) in C::decompose_tensor(&t.2) {
            out.push(((A::sdql_zero(), B::sdql_zero(), c_left, D::sdql_zero(), E::sdql_zero(), F::sdql_zero(), G::sdql_zero()), r));
        }
        for (d_left, r) in D::decompose_tensor(&t.3) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), d_left, E::sdql_zero(), F::sdql_zero(), G::sdql_zero()), r));
        }
        for (e_left, r) in E::decompose_tensor(&t.4) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), e_left, F::sdql_zero(), G::sdql_zero()), r));
        }
        for (f_left, r) in F::decompose_tensor(&t.5) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), f_left, G::sdql_zero()), r));
        }
        for (g_left, r) in G::decompose_tensor(&t.6) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), F::sdql_zero(), g_left), r));
        }
        out
    }
}

impl<R: Clone, A: TensorLeft<R> + SdqlZero, B: TensorLeft<R> + SdqlZero, C: TensorLeft<R> + SdqlZero, D: TensorLeft<R> + SdqlZero, E: TensorLeft<R> + SdqlZero, F: TensorLeft<R> + SdqlZero, G: TensorLeft<R> + SdqlZero, H: TensorLeft<R> + SdqlZero> TensorLeft<R> for (A, B, C, D, E, F, G, H) {
    type Tensor = (A::Tensor, B::Tensor, C::Tensor, D::Tensor, E::Tensor, F::Tensor, G::Tensor, H::Tensor);
    fn mk_tensor_left(a: &Self, b: &R) -> Self::Tensor {
        (A::mk_tensor_left(&a.0, b), B::mk_tensor_left(&a.1, b), C::mk_tensor_left(&a.2, b), D::mk_tensor_left(&a.3, b), E::mk_tensor_left(&a.4, b), F::mk_tensor_left(&a.5, b), G::mk_tensor_left(&a.6, b), H::mk_tensor_left(&a.7, b))
    }
    fn decompose_tensor(t: &Self::Tensor) -> Vec<(Self, R)> {
        let mut out = Vec::new();
        for (a_left, r) in A::decompose_tensor(&t.0) {
            out.push(((a_left, B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), F::sdql_zero(), G::sdql_zero(), H::sdql_zero()), r));
        }
        for (b_left, r) in B::decompose_tensor(&t.1) {
            out.push(((A::sdql_zero(), b_left, C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), F::sdql_zero(), G::sdql_zero(), H::sdql_zero()), r));
        }
        for (c_left, r) in C::decompose_tensor(&t.2) {
            out.push(((A::sdql_zero(), B::sdql_zero(), c_left, D::sdql_zero(), E::sdql_zero(), F::sdql_zero(), G::sdql_zero(), H::sdql_zero()), r));
        }
        for (d_left, r) in D::decompose_tensor(&t.3) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), d_left, E::sdql_zero(), F::sdql_zero(), G::sdql_zero(), H::sdql_zero()), r));
        }
        for (e_left, r) in E::decompose_tensor(&t.4) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), e_left, F::sdql_zero(), G::sdql_zero(), H::sdql_zero()), r));
        }
        for (f_left, r) in F::decompose_tensor(&t.5) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), f_left, G::sdql_zero(), H::sdql_zero()), r));
        }
        for (g_left, r) in G::decompose_tensor(&t.6) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), F::sdql_zero(), g_left, H::sdql_zero()), r));
        }
        for (h_left, r) in H::decompose_tensor(&t.7) {
            out.push(((A::sdql_zero(), B::sdql_zero(), C::sdql_zero(), D::sdql_zero(), E::sdql_zero(), F::sdql_zero(), G::sdql_zero(), h_left), r));
        }
        out
    }
}

impl<V> SdqlSemiringTensor<V> for <V as TensorLeft<V>>::Tensor
where
    V: TensorLeft<V> + SdqlBilinear + Clone,
    V::Scalar: SdqlAdd + SdqlZero + SdqlOne,
    <V as TensorLeft<V>>::Tensor: SdqlScale<V::Scalar> + SdqlZero + SdqlAdd,
{
    type Scalar = V::Scalar;
    fn decompose(&self) -> Vec<(V, V)> {
        V::decompose_tensor(self)
    }
    fn mk_tensor(a: &V, b: &V) -> Self {
        V::mk_tensor_left(a, b)
    }
    fn bilinear(a: &V, b: &V) -> Self::Scalar {
        V::sdql_bilinear(a, b)
    }
    fn scale(s: &Self::Scalar, t: &Self) -> Self {
        <Self as SdqlScale<Self::Scalar>>::sdql_scale(s, t)
    }
    fn zero() -> Self {
        <Self as SdqlZero>::sdql_zero()
    }
    fn add(a: &Self, b: &Self) -> Self {
        a.sdql_add(b)
    }
}

// ============================================================================
// Dictionary and Tuple Helpers
// ============================================================================

/// Insert into a BTreeMap without mutation at the call-site.
/// Returns a new map with the key-value pair inserted.
pub fn map_insert<K: Ord, V>(mut m: BTreeMap<K, V>, k: K, v: V) -> BTreeMap<K, V> {
    m.insert(k, v);
    m
}

/// Lookup a key in a BTreeMap, returning a default value if not found.
pub fn lookup_or_default<K: Ord, V: Clone>(m: &BTreeMap<K, V>, k: K, default: V) -> V {
    match m.get(&k) {
        Some(v) => v.clone(),
        None => default,
    }
}

/// Dictionary addition: merges two BTreeMaps by adding values for shared keys.
pub fn dict_add<K: Ord + Clone, V: SdqlAdd + Clone>(a: BTreeMap<K, V>, b: BTreeMap<K, V>) -> BTreeMap<K, V> {
    let mut acc = a;
    for (k, v2) in b.into_iter() {
        if let Some(v1) = acc.get(&k) {
            let new_v = v1.sdql_add(&v2);
            acc.insert(k.clone(), new_v);
        } else {
            acc.insert(k, v2);
        }
    }
    acc
}

pub fn sdql_semiring_mul<T, V>(a: T, b: T) -> T
where
    T: SdqlSemiringTensor<V>,
{
    let left = a.decompose();
    let right = b.decompose();
    let mut acc = T::zero();
    for (a_left, b_left) in left.into_iter() {
        for pair in right.iter() {
            let x = &pair.0;
            let y = &pair.1;
            let scalar = T::bilinear(&b_left, x);
            let tensor = T::mk_tensor(&a_left, y);
            let scaled = T::scale(&scalar, &tensor);
            acc = T::add(&acc, &scaled);
        }
    }
    acc
}

pub fn sdql_closure<T>(_a: T) -> T {
    todo!("sdql_closure for square matrices not implemented")
}

/// Tuple/record addition for arity 0.
pub fn tuple_add0(a: (), _b: ()) -> () { a }

/// Tuple/record addition for arity 1.
pub fn tuple_add<T1: SdqlAdd>(a: (T1,), b: (T1,)) -> (T1,) {
    (a.0.sdql_add(&b.0),)
}

/// Tuple/record addition for arity 2.
pub fn tuple_add2<T1: SdqlAdd, T2: SdqlAdd>(a: (T1, T2), b: (T1, T2)) -> (T1, T2) {
    (a.0.sdql_add(&b.0), a.1.sdql_add(&b.1))
}

/// Tuple/record addition for arity 3.
pub fn tuple_add3<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd>(a: (T1, T2, T3), b: (T1, T2, T3)) -> (T1, T2, T3) {
    (a.0.sdql_add(&b.0), a.1.sdql_add(&b.1), a.2.sdql_add(&b.2))
}

/// Tuple/record addition for arity 4.
pub fn tuple_add4<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd>(a: (T1, T2, T3, T4), b: (T1, T2, T3, T4)) -> (T1, T2, T3, T4) {
    (a.0.sdql_add(&b.0), a.1.sdql_add(&b.1), a.2.sdql_add(&b.2), a.3.sdql_add(&b.3))
}

/// Tuple/record addition for arity 5.
pub fn tuple_add5<T1: SdqlAdd, T2: SdqlAdd, T3: SdqlAdd, T4: SdqlAdd, T5: SdqlAdd>(a: (T1, T2, T3, T4, T5), b: (T1, T2, T3, T4, T5)) -> (T1, T2, T3, T4, T5) {
    (a.0.sdql_add(&b.0), a.1.sdql_add(&b.1), a.2.sdql_add(&b.2), a.3.sdql_add(&b.3), a.4.sdql_add(&b.4))
}

// ============================================================================
// Scalar Promotion + MaxProduct helpers
// ============================================================================

pub fn promote_max_product(x: Real) -> MaxProduct { MaxProduct(x) }

pub fn demote_max_product(x: MaxProduct) -> Real { x.0 }

pub fn promote_int_to_real(x: i64) -> Real { Real::new(x as f64) }

pub fn promote_int_to_max_product(x: i64) -> MaxProduct { MaxProduct(promote_int_to_real(x)) }

pub fn max_product_add(a: MaxProduct, b: MaxProduct) -> MaxProduct { std::cmp::max(a, b) }

// ============================================================================
// Extension Functions (Builtins)
// ============================================================================

pub fn ext_and(args: (bool, bool)) -> bool { args.0 && args.1 }

pub fn ext_or(args: (bool, bool)) -> bool { args.0 || args.1 }

pub fn ext_eq<T: PartialEq>(args: (T, T)) -> bool { args.0 == args.1 }

pub fn ext_leq<T: PartialOrd>(args: (T, T)) -> bool { args.0 <= args.1 }

pub fn ext_lt<T: PartialOrd>(args: (T, T)) -> bool { args.0 < args.1 }

pub fn ext_sub<T: std::ops::Sub<Output = T>>(args: (T, T)) -> T { args.0 - args.1 }

pub fn ext_div(args: (Real, Real)) -> Real { Real(args.0.0 / args.1.0) }

pub fn ext_str_ends_with(args: (String, String)) -> bool {
    let (s, suf) = args;
    s.ends_with(&suf)
}

pub fn ext_str_starts_with(args: (String, String)) -> bool {
    let (s, pre) = args;
    s.starts_with(&pre)
}

pub fn ext_str_contains(args: (String, String)) -> bool {
    let (s, sub) = args;
    s.contains(&sub)
}

pub fn ext_first_index(args: (String, String)) -> i64 {
    let (s, pat) = args;
    s.find(&pat).map(|i| i as i64).unwrap_or(-1)
}

pub fn ext_last_index(args: (String, String)) -> i64 {
    let (s, pat) = args;
    s.rfind(&pat).map(|i| i as i64).unwrap_or(-1)
}

/// Return the substring `s[start..end]` (byte indices, end exclusive).
///
/// This matches the sdql-rs backend behavior for `ext(\`SubString\`, s, start, end)`.
pub fn ext_sub_string(args: (String, i64, i64)) -> String {
    let (s, start, end) = args;
    let bytes = s.as_bytes();
    let start: usize = if start <= 0 { 0 } else { (start as u64).min(usize::MAX as u64) as usize };
    let end: usize = if end <= 0 { 0 } else { (end as u64).min(usize::MAX as u64) as usize };
    let start = start.min(bytes.len());
    let end = end.min(bytes.len());
    if start >= end {
        return String::new();
    }
    String::from_utf8_lossy(&bytes[start..end]).into_owned()
}

/// Extract the year from a YYYYMMDD-encoded SDQL Date.
pub fn ext_year(d: Date) -> i64 { d.0 / 10000 }

/// Extract the domain (key set) of a dictionary.
pub fn ext_dom<K: Ord + Clone, V>(m: &BTreeMap<K, V>) -> BTreeMap<K, bool> {
    let mut out = BTreeMap::new();
    for k in m.keys() {
        out.insert(k.clone(), true);
    }
    out
}

/// Return the number of entries in a dictionary.
pub fn ext_size<K: Ord, V>(m: &BTreeMap<K, V>) -> i64 {
    m.len() as i64
}

/// Generate a range dictionary {0 -> true, 1 -> true, ..., n-1 -> true}.
pub fn ext_range(n: i64) -> BTreeMap<i64, bool> {
    let mut out = BTreeMap::new();
    let mut i = 0;
    while i < n {
        out.insert(i, true);
        i += 1;
    }
    out
}

// ============================================================================
// Concat (Record Concatenation)
// ============================================================================

// Generic concat trait - concatenates two records/tuples into one
pub trait Concat<B> {
    type Output;
    fn concat(self, other: B) -> Self::Output;
}

// Unit concatenation
impl<B> Concat<B> for () {
    type Output = B;
    fn concat(self, other: B) -> Self::Output { other }
}

macro_rules! impl_concat_tuple {
    ([$($T:ident : $t:ident),+], [$($U:ident : $u:ident),*]) => {
        impl<$($T,)* $($U,)*> Concat<($($U,)*)> for ($($T,)*) {
            type Output = ($($T,)* $($U,)*);
            fn concat(self, other: ($($U,)*)) -> Self::Output {
                let ($($t,)*) = self;
                let ($($u,)*) = other;
                ($($t,)* $($u,)*)
            }
        }
    };
}

// Concatenation implementations for tuples up to total arity 8.
impl_concat_tuple!([T1: t1], []);
impl_concat_tuple!([T1: t1], [U1: u1]);
impl_concat_tuple!([T1: t1], [U1: u1, U2: u2]);
impl_concat_tuple!([T1: t1], [U1: u1, U2: u2, U3: u3]);
impl_concat_tuple!([T1: t1], [U1: u1, U2: u2, U3: u3, U4: u4]);
impl_concat_tuple!([T1: t1], [U1: u1, U2: u2, U3: u3, U4: u4, U5: u5]);
impl_concat_tuple!([T1: t1], [U1: u1, U2: u2, U3: u3, U4: u4, U5: u5, U6: u6]);
impl_concat_tuple!([T1: t1], [U1: u1, U2: u2, U3: u3, U4: u4, U5: u5, U6: u6, U7: u7]);

impl_concat_tuple!([T1: t1, T2: t2], []);
impl_concat_tuple!([T1: t1, T2: t2], [U1: u1]);
impl_concat_tuple!([T1: t1, T2: t2], [U1: u1, U2: u2]);
impl_concat_tuple!([T1: t1, T2: t2], [U1: u1, U2: u2, U3: u3]);
impl_concat_tuple!([T1: t1, T2: t2], [U1: u1, U2: u2, U3: u3, U4: u4]);
impl_concat_tuple!([T1: t1, T2: t2], [U1: u1, U2: u2, U3: u3, U4: u4, U5: u5]);
impl_concat_tuple!([T1: t1, T2: t2], [U1: u1, U2: u2, U3: u3, U4: u4, U5: u5, U6: u6]);

impl_concat_tuple!([T1: t1, T2: t2, T3: t3], []);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3], [U1: u1]);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3], [U1: u1, U2: u2]);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3], [U1: u1, U2: u2, U3: u3]);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3], [U1: u1, U2: u2, U3: u3, U4: u4]);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3], [U1: u1, U2: u2, U3: u3, U4: u4, U5: u5]);

impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4], []);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4], [U1: u1]);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4], [U1: u1, U2: u2]);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4], [U1: u1, U2: u2, U3: u3]);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4], [U1: u1, U2: u2, U3: u3, U4: u4]);

impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4, T5: t5], []);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4, T5: t5], [U1: u1]);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4, T5: t5], [U1: u1, U2: u2]);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4, T5: t5], [U1: u1, U2: u2, U3: u3]);

impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4, T5: t5, T6: t6], []);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4, T5: t5, T6: t6], [U1: u1]);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4, T5: t5, T6: t6], [U1: u1, U2: u2]);

impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4, T5: t5, T6: t6, T7: t7], []);
impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4, T5: t5, T6: t6, T7: t7], [U1: u1]);

impl_concat_tuple!([T1: t1, T2: t2, T3: t3, T4: t4, T5: t5, T6: t6, T7: t7, T8: t8], []);

/// Concatenate two records (tuples).
/// args: a pair of tuples
/// Returns the concatenation of the two tuples.
pub fn ext_concat<A, B>(args: (A, B)) -> <A as Concat<B>>::Output
where
    A: Concat<B>,
{
    args.0.concat(args.1)
}

// ============================================================================
// TBL File Loading
// ============================================================================

/// Trait for parsing a TBL field string into a typed value.
pub trait FromTblField: Sized + Default {
    fn from_tbl_field(s: &str) -> Self;
}

impl FromTblField for i64 {
    fn from_tbl_field(s: &str) -> Self { s.parse().unwrap_or(0) }
}

impl FromTblField for String {
    fn from_tbl_field(s: &str) -> Self { s.to_string() }
}

impl FromTblField for Real {
    fn from_tbl_field(s: &str) -> Self { Real::new(s.parse().unwrap_or(0.0)) }
}

impl FromTblField for MaxProduct {
    fn from_tbl_field(s: &str) -> Self { MaxProduct(Real::from_tbl_field(s)) }
}

impl FromTblField for bool {
    fn from_tbl_field(s: &str) -> Self { s == "true" || s == "1" }
}

impl FromTblField for Date {
    fn from_tbl_field(s: &str) -> Self {
        // Parse date in format YYYY-MM-DD to YYYYMMDD
        let parts: Vec<&str> = s.split('-').collect();
        if parts.len() == 3 {
            let y: i64 = parts[0].parse().unwrap_or(0);
            let m: i64 = parts[1].parse().unwrap_or(0);
            let d: i64 = parts[2].parse().unwrap_or(0);
            Date::new(y * 10000 + m * 100 + d)
        } else {
            // Try parsing as YYYYMMDD directly
            Date::new(s.parse().unwrap_or(0))
        }
    }
}

/// Parses a TBL file into rows of string fields.
fn parse_tbl_lines(path: &str) -> Vec<Vec<String>> {
    let file = File::open(path).unwrap_or_else(|_| panic!("Failed to open {}", path));
    let reader = BufReader::new(file);
    let mut rows = Vec::new();
    for line in reader.lines() {
        let line = line.expect("Failed to read line");
        // TBL format: field1|field2|...|fieldN|  (trailing pipe)
        let fields: Vec<String> = line.trim_end_matches('|').split('|').map(|s| s.to_string()).collect();
        rows.push(fields);
    }
    rows
}

/// Resolve TPCH dataset paths at runtime.
///
/// When SDQL programs refer to files under `datasets/tpch/...`, tests can override the base
/// directory by setting `TPCH_DATASET_PATH` (e.g. to `datasets/tpch-tiny`).
fn resolve_tbl_path(path: &str) -> String {
    const PREFIX: &str = "datasets/tpch/";
    if let Some(rest) = path.strip_prefix(PREFIX) {
        let base = std::env::var("TPCH_DATASET_PATH").unwrap_or_else(|_| "datasets/tpch".to_string());
        let base = base.trim_end_matches('/');
        if rest.is_empty() {
            base.to_string()
        } else {
            format!("{}/{}", base, rest)
        }
    } else {
        path.to_string()
    }
}

/// Generic column builder: parses column `col` from each row into a BTreeMap<i64, T>.
pub fn build_col<T: FromTblField>(rows: &[Vec<String>], col: usize) -> BTreeMap<i64, T> {
    let mut m = BTreeMap::new();
    for (i, row) in rows.iter().enumerate() {
        let v = row.get(col).map(|s| T::from_tbl_field(s)).unwrap_or_default();
        m.insert(i as i64, v);
    }
    m
}

/// Generic TBL loader: parses a TBL file and returns (rows, size).
/// Callers use build_col to extract typed columns.
pub fn load_tbl(path: &str) -> (Vec<Vec<String>>, i64) {
    let resolved = resolve_tbl_path(path);
    let rows = parse_tbl_lines(&resolved);
    let size = rows.len() as i64;
    (rows, size)
}

// ============================================================================
// Pretty-Printing (SDQLShow)
// ============================================================================

/// Trait for pretty-printing SDQL values, mirroring Lean's showValue.
pub trait SDQLShow {
    fn show(&self) -> String;
}

impl SDQLShow for i64 {
    fn show(&self) -> String { self.to_string() }
}

impl SDQLShow for Real {
    fn show(&self) -> String { self.0.to_string() }
}

impl SDQLShow for MaxProduct {
    fn show(&self) -> String { self.0.show() }
}

impl SDQLShow for Date {
    fn show(&self) -> String { format!("date({})", self.0) }
}

impl SDQLShow for bool {
    fn show(&self) -> String { self.to_string() }
}

impl SDQLShow for String {
    fn show(&self) -> String { format!("\"{}\"", self) }
}

impl<K: Ord + SDQLShow, V: SDQLShow> SDQLShow for BTreeMap<K, V> {
    fn show(&self) -> String {
        let mut s = String::new();
        s.push('{');
        for (k, v) in self.iter() {
            s.push_str(&format!("{} -> {}, ", k.show(), v.show()));
        }
        s.push('}');
        s
    }
}

// Tuple/record pretty-printing for arities 1-8
impl<T1: SDQLShow> SDQLShow for (T1,) {
    fn show(&self) -> String { format!("<{}>", self.0.show()) }
}

impl<T1: SDQLShow, T2: SDQLShow> SDQLShow for (T1, T2) {
    fn show(&self) -> String { format!("<{}, {}>", self.0.show(), self.1.show()) }
}

impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow> SDQLShow for (T1, T2, T3) {
    fn show(&self) -> String { format!("<{}, {}, {}>", self.0.show(), self.1.show(), self.2.show()) }
}

impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow> SDQLShow for (T1, T2, T3, T4) {
    fn show(&self) -> String { format!("<{}, {}, {}, {}>", self.0.show(), self.1.show(), self.2.show(), self.3.show()) }
}

impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5) {
    fn show(&self) -> String { format!("<{}, {}, {}, {}, {}>", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show()) }
}

impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow, T6: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5, T6) {
    fn show(&self) -> String { format!("<{}, {}, {}, {}, {}, {}>", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show(), self.5.show()) }
}

impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow, T6: SDQLShow, T7: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5, T6, T7) {
    fn show(&self) -> String { format!("<{}, {}, {}, {}, {}, {}, {}>", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show(), self.5.show(), self.6.show()) }
}

impl<T1: SDQLShow, T2: SDQLShow, T3: SDQLShow, T4: SDQLShow, T5: SDQLShow, T6: SDQLShow, T7: SDQLShow, T8: SDQLShow> SDQLShow for (T1, T2, T3, T4, T5, T6, T7, T8) {
    fn show(&self) -> String { format!("<{}, {}, {}, {}, {}, {}, {}, {}>", self.0.show(), self.1.show(), self.2.show(), self.3.show(), self.4.show(), self.5.show(), self.6.show(), self.7.show()) }
}
