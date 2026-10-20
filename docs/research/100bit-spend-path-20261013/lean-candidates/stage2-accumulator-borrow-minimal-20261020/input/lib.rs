#![allow(dead_code)]
extern crate alloc;
use alloc::vec::Vec;

pub struct Accumulator {
    pub weights: Vec<u32>,
    pub rhs: u32,
    pub power: u32,
    pub next: usize,
}

pub struct Pending {
    pub raw: Vec<u32>,
    pub terms: usize,
}

impl Pending {
    pub fn push(&mut self, index: usize, value: u32) {
        self.raw[index] = value;
    }
}

pub struct State {
    pub accumulator: Accumulator,
    pub pending: Pending,
}

#[derive(Clone, Copy)]
pub struct Field(pub u32);

impl Field {
    pub fn mul(self, _rhs: Self) -> Self { self }
    pub fn double(self) -> Self { self }
    pub fn sub(self, _rhs: Self) -> Self { self }
}

fn observer(_index: usize, _value: u32) {}

fn update_fields(a: &mut Accumulator) {
    for j in 0..a.weights.len() {
        a.weights[j] = a.power;
    }
    a.rhs = a.power;
    a.next = 1;
}

fn update_with_separate_mutable_call(a: &mut Accumulator, b: &mut Pending) {
    for j in 0..a.weights.len() {
        b.push(j, a.power);
        a.weights[j] = a.power;
    }
    a.rhs = a.power;
    a.next = 1;
}

fn update_with_optional_mutable_call(a: &mut Accumulator, mut node: Field, mut pending: Option<&mut Pending>) {
    let mut basis = [Field(a.power); 4];
    basis[0] = Field(1);
    let mut n = 1;
    while n < a.weights.len() {
        for j in 0..n {
            basis[n + j] = basis[j].mul(node);
        }
        node = node.mul(node).double().sub(Field(1));
        n = a.weights.len();
    }
    for j in 0..a.weights.len() {
        if let Some(b) = pending.as_deref_mut() {
            b.push(j, a.power);
        }
        a.weights[j] = basis[j].0;
        observer(j, a.weights[j]);
        observer(j, a.power);
    }
    a.rhs = a.power;
    a.next = 1;
    if let Some(b) = pending {
        b.terms = 1;
    }
}

fn update_with_observer(a: &mut Accumulator) {
    for j in 0..a.weights.len() {
        a.weights[j] = a.power;
        observer(j, a.weights[j]);
    }
    a.rhs = a.power;
    a.next = 1;
}

pub fn case_fields(state: &mut State) {
    update_fields(&mut state.accumulator);
    state.pending.terms = 1;
}

pub fn case_disjoint_fields(state: &mut State) {
    update_with_separate_mutable_call(&mut state.accumulator, &mut state.pending);
}

pub fn case_option_reborrow(state: &mut State) {
    let node = Field(state.accumulator.power);
    update_with_optional_mutable_call(&mut state.accumulator, node, Some(&mut state.pending));
}

pub fn case_observer(state: &mut State) {
    update_with_observer(&mut state.accumulator);
}
