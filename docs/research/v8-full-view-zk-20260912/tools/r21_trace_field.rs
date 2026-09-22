//! Host-only symbolic QM31 used by the R21 public-arithmetic trace.
//!
//! This module deliberately contains no proof machinery.  `K` values carry a
//! node id into a thread-local arena; arithmetic methods have the same names
//! as the native field API, so the retained source can be included unchanged.
extern crate aspis_core as native_core;

use std::cell::RefCell;
use std::collections::HashMap;

pub use native_core::field::M31;
pub const M31_HALF: M31 = native_core::field::M31_HALF;

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum Node {
    Input(usize),
    Const([u32; 4]),
    Add(u32, u32),
    Mul(u32, u32),
    Sub(u32, u32),
}

#[derive(Default)]
struct Arena {
    nodes: Vec<Node>,
    cse: HashMap<Node, u32>,
}

thread_local! { static ARENA: RefCell<Arena> = RefCell::new(Arena::new()); }

impl Arena {
    fn new() -> Self {
        let mut a = Self {
            nodes: Vec::new(),
            cse: HashMap::new(),
        };
        a.intern(Node::Const([0; 4]));
        a.intern(Node::Const([1, 0, 0, 0]));
        a
    }
    fn intern(&mut self, n: Node) -> u32 {
        if let Some(&id) = self.cse.get(&n) {
            return id;
        }
        let id = self.nodes.len() as u32;
        self.nodes.push(n);
        self.cse.insert(n, id);
        id
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct K(pub u32);

impl K {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    pub fn input(index: usize) -> Self {
        ARENA.with(|a| Self(a.borrow_mut().intern(Node::Input(index))))
    }
    pub fn from_native(v: native_core::field::QM31) -> Self {
        let mut bytes = [0u8; 16];
        v.write_le_bytes(&mut bytes);
        let mut limbs = [0u32; 4];
        for i in 0..4 {
            limbs[i] = u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap());
        }
        ARENA.with(|a| Self(a.borrow_mut().intern(Node::Const(limbs))))
    }
    pub fn from_cm31(v: native_core::field::CM31) -> Self {
        Self::from_native(native_core::field::QM31::from_cm31(v))
    }
    pub fn from_m31(v: M31) -> Self {
        Self::from_native(native_core::field::QM31::from_cm31(
            native_core::field::CM31::from_m31(v),
        ))
    }
    pub fn native(self, inputs: &[native_core::field::QM31]) -> native_core::field::QM31 {
        eval_node(self.0, inputs)
    }
    fn constant(self) -> Option<native_core::field::QM31> {
        ARENA.with(|a| match a.borrow().nodes.get(self.0 as usize) {
            Some(Node::Const(l)) => {
                let mut b = [0u8; 16];
                for i in 0..4 {
                    b[4 * i..4 * i + 4].copy_from_slice(&l[i].to_le_bytes());
                }
                native_core::field::QM31::from_le_bytes(&b)
            }
            _ => None,
        })
    }
    fn bin(self, rhs: Self, op: Op) -> Self {
        if self == Self::ZERO {
            if matches!(op, Op::Add) {
                return rhs;
            }
            if matches!(op, Op::Mul) {
                return Self::ZERO;
            }
        }
        if rhs == Self::ZERO {
            if matches!(op, Op::Add | Op::Sub) {
                return self;
            }
            if matches!(op, Op::Mul) {
                return Self::ZERO;
            }
        }
        if matches!(op, Op::Mul) && (self == Self::ONE) {
            return rhs;
        }
        if matches!(op, Op::Mul) && (rhs == Self::ONE) {
            return self;
        }
        if matches!(op, Op::Sub) && self == rhs {
            return Self::ZERO;
        }
        if let (Some(a), Some(b)) = (self.constant(), rhs.constant()) {
            let v = match op {
                Op::Add => a.add(b),
                Op::Mul => a.mul(b),
                Op::Sub => a.sub(b),
            };
            return Self::from_native(v);
        }
        ARENA.with(|a| {
            Self(a.borrow_mut().intern(match op {
                Op::Add => Node::Add(self.0, rhs.0),
                Op::Mul => Node::Mul(self.0, rhs.0),
                Op::Sub => Node::Sub(self.0, rhs.0),
            }))
        })
    }
    pub fn add(self, rhs: Self) -> Self {
        self.bin(rhs, Op::Add)
    }
    pub fn sub(self, rhs: Self) -> Self {
        self.bin(rhs, Op::Sub)
    }
    pub fn mul(self, rhs: Self) -> Self {
        self.bin(rhs, Op::Mul)
    }
    pub fn neg(self) -> Self {
        Self::ZERO.sub(self)
    }
    pub fn square(self) -> Self {
        self.mul(self)
    }
    pub fn half(self) -> Self {
        self.mul_m31(M31_HALF)
    }
    pub fn double(self) -> Self {
        self.add(self)
    }
    pub fn pow(self, mut n: u32) -> Self {
        let mut b = self;
        let mut r = Self::ONE;
        while n != 0 {
            if n & 1 != 0 {
                r = r.mul(b);
            }
            n >>= 1;
            if n != 0 {
                b = b.square();
            }
        }
        r
    }
    pub fn mul_m31(self, rhs: M31) -> Self {
        self.mul(Self::from_m31(rhs))
    }
    pub fn try_inv(self) -> Option<Self> {
        panic!("inversion is not supported in the fixed polynomial circuit")
    }
}

enum Op {
    Add,
    Mul,
    Sub,
}

fn eval_node(id: u32, inputs: &[native_core::field::QM31]) -> native_core::field::QM31 {
    let nodes=nodes();
    let mut values:Vec<native_core::field::QM31>=Vec::with_capacity(nodes.len());
    for n in nodes.into_iter().take(id as usize+1) {
    let v=match n {
        Node::Input(i) => inputs
            .get(i)
            .copied()
            .expect("missing public circuit input"),
        Node::Const(l) => {
            let mut b = [0u8; 16];
            for i in 0..4 {
                b[4 * i..4 * i + 4].copy_from_slice(&l[i].to_le_bytes());
            }
            native_core::field::QM31::from_le_bytes(&b).unwrap()
        }
        Node::Add(a, b) => values[a as usize].add(values[b as usize]),
        Node::Mul(a, b) => values[a as usize].mul(values[b as usize]),
        Node::Sub(a, b) => values[a as usize].sub(values[b as usize]),
    };values.push(v);
    } values[id as usize]
}

#[derive(Clone, Copy)]
pub struct PreparedQm31Multiplier(pub K);
impl PreparedQm31Multiplier {
    pub fn new(v: K) -> Self {
        Self(v)
    }
    pub fn mul(self, rhs: K) -> K {
        self.0.mul(rhs)
    }
}

pub fn qm31_sum_products4(left: [K; 4], right: [K; 4]) -> K {
    left.into_iter()
        .zip(right)
        .fold(K::ZERO, |s, (a, b)| s.add(a.mul(b)))
}
pub fn dot(left: &[K], right: &[K]) -> K {
    assert_eq!(left.len(), right.len());
    left.iter().zip(right).fold(K::ZERO, |s, (&a, &b)| s.add(a.mul(b)))
}
pub fn qm31_sum_products3(left: [K; 3], right: [K; 3]) -> K {
    left.into_iter()
        .zip(right)
        .fold(K::ZERO, |s, (a, b)| s.add(a.mul(b)))
}
pub fn qm31_sum_products3_prepared(left: &[PreparedQm31Multiplier; 3], right: &[K; 3]) -> K {
    (0..3).fold(K::ZERO, |s, i| s.add(left[i].mul(right[i])))
}
pub fn qm31_sum_products2_prepared(left: &[PreparedQm31Multiplier; 2], right: &[K; 2]) -> K {
    (0..2).fold(K::ZERO, |s, i| s.add(left[i].mul(right[i])))
}

pub fn reset() {
    ARENA.with(|a| *a.borrow_mut() = Arena::new());
}
pub fn nodes() -> Vec<Node> {
    ARENA.with(|a| a.borrow().nodes.clone())
}
pub fn eval_dag(inputs: &[native_core::field::QM31], output: K) -> native_core::field::QM31 {
    output.native(inputs)
}

pub mod field {
    pub use super::dot as qm31_dot;
    pub use super::{
        qm31_sum_products2_prepared, qm31_sum_products3, qm31_sum_products3_prepared,
        qm31_sum_products4, dot, PreparedQm31Multiplier, K as QM31, M31, M31_HALF,
    };
    pub use crate::native_core::field::{CM31, P};
}

pub mod v6_transcript {
    use super::K;
    pub const V6_SEMANTIC_ROUNDS: usize = 10;
    pub fn v6_statement_points(z: &[K; V6_SEMANTIC_ROUNDS]) -> [[K; 10]; 3] {
        let mut successor = *z;
        let last = z.len() - 1;
        successor[last] = K::ONE.sub(z[last]);
        let mut carry = z[last];
        for coordinate in (0..last).rev() {
            let bit = z[coordinate];
            let bac = bit.mul(carry);
            successor[coordinate] = bit.add(carry).sub(bac.add(bac));
            carry = bac;
        }
        let mut xor12 = *z;
        for coordinate in [7usize, 6] {
            xor12[coordinate] = K::ONE.sub(xor12[coordinate]);
        }
        [*z, successor, xor12]
    }
}

fn eval_unused() {}
