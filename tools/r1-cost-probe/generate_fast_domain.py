#!/usr/bin/env python3
"""Generate the exact two-table factorization used by fast_domain.rs."""

from __future__ import annotations

import argparse
from pathlib import Path
import sys


P = (1 << 31) - 1
GENERATOR = (2, 1268011823)
TABLE_SIZE = 512
ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / "crates/aspis-core/src/fast_domain.rs"


def reverse9(value: int) -> int:
    result = 0
    for _ in range(9):
        result = (result << 1) | (value & 1)
        value >>= 1
    return result


def multiply(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    a, b = left
    c, d = right
    return ((a * c - b * d) % P, (a * d + b * c) % P)


def power(base: tuple[int, int], exponent: int) -> tuple[int, int]:
    result = (1, 0)
    while exponent:
        if exponent & 1:
            result = multiply(result, base)
        base = multiply(base, base)
        exponent >>= 1
    return result


def render_table(name: str, values: list[tuple[int, int]]) -> str:
    rows = []
    for start in range(0, len(values), 4):
        group = values[start : start + 4]
        rows.append("    " + ", ".join(f"({a}, {b})" for a, b in group) + ",")
    return f"const {name}: [(u32, u32); 512] = [\n" + "\n".join(rows) + "\n];\n"


def generate() -> str:
    table_a = [power(GENERATOR, 1024 + 4096 * (reverse9(lo) << 9)) for lo in range(TABLE_SIZE)]
    table_b = [power(GENERATOR, 4096 * reverse9(hi)) for hi in range(TABLE_SIZE)]
    return """//! Exact, factored evaluation of the checked R0 fibre domain.
//!
//! For u = 512*hi + lo, reversing its 18 bits gives
//! `rev18(u) = (reverse9(lo) << 9) + reverse9(hi)`. Therefore the specified
//! point `g^(1024 + 4096*rev18(u))` is exactly the product of the A and B
//! table entries below. These generated constants only replace exponentiation
//! with two indexed loads and one CM31 multiplication; the domain, generator,
//! index map, and protocol behavior are unchanged.

use crate::field::{CM31, M31};
use crate::r0::domain::{FibreIndex, Point};

""" + render_table("TABLE_A", table_a) + "\n" + render_table("TABLE_B", table_b) + """
#[inline]
fn table_value(value: (u32, u32)) -> CM31 {
    CM31::new(M31(value.0), M31(value.1))
}

/// Return exactly the core R0 fibre point for this checked index.
#[inline]
pub fn fibre_point(u: FibreIndex) -> Point<M31> {
    let index = u.get();
    let left = table_value(TABLE_A[index & 511]);
    let right = table_value(TABLE_B[index >> 9]);
    let point = left.mul(right);
    Point {
        x: point.a,
        y: point.b,
    }
}

/// Return the R0 line node `2*x^2 - 1` for this checked fibre index.
#[inline]
pub fn line_node(u: FibreIndex) -> M31 {
    let x = fibre_point(u).x;
    let square = x.mul(x);
    square.double().sub(M31::ONE)
}
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="fail if the checked-in Rust source is stale")
    args = parser.parse_args()
    generated = generate()
    if args.check:
        try:
            existing = OUTPUT.read_text()
        except FileNotFoundError:
            print(f"missing generated source: {OUTPUT}", file=sys.stderr)
            return 1
        if existing != generated:
            print(f"generated source is stale: {OUTPUT}", file=sys.stderr)
            return 1
        print(f"generated source is current: {OUTPUT}")
        return 0
    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    OUTPUT.write_text(generated)
    print(f"wrote {OUTPUT}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
