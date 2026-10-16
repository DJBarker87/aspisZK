//! SPEC §3: checked Fin indices and the exact stored circle domain.

use super::{basis, CodeField, Error, FIBRE_COUNT, WORD_LEN};
use crate::field::{CM31, M31};

macro_rules! index_type {
    ($name:ident, $bound:expr) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub struct $name(usize);
        impl $name {
            pub fn new(index: usize) -> Result<Self, Error> {
                if index < $bound {
                    Ok(Self(index))
                } else {
                    Err(Error::IndexOutOfRange)
                }
            }
            pub const fn get(self) -> usize {
                self.0
            }
        }
    };
}
index_type!(FibreIndex, FIBRE_COUNT);
index_type!(SlotIndex, 4);
index_type!(InitialIndex, WORD_LEN);

/// Coordinates over F, K or E. Construction itself does not assert circle
/// membership or the non-base/distinct hypotheses of the chord theorem.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Point<E> {
    pub x: E,
    pub y: E,
}

impl<E: CodeField> Point<E> {
    pub fn is_on_circle(self) -> bool {
        self.x.mul(self.x).add(self.y.mul(self.y)) == E::ONE
    }
}

/// SPEC §3: Fin 2^18 × Fin 4 → Fin 2^20, consecutive children.
pub const fn child_index(u: FibreIndex, s: SlotIndex) -> InitialIndex {
    InitialIndex(4 * u.0 + s.0)
}
pub const fn parent_index(i: InitialIndex) -> FibreIndex {
    FibreIndex(i.0 / 4)
}
pub const fn slot_index(i: InitialIndex) -> SlotIndex {
    SlotIndex(i.0 % 4)
}
pub fn rev18(u: FibreIndex) -> usize {
    (u.0 as u32).reverse_bits() as usize >> 14
}

/// SPEC §3: the natural index n(i), before the stored permutation.
pub fn natural_index(i: InitialIndex) -> usize {
    let r = rev18(parent_index(i));
    match slot_index(i).0 {
        0 => 2 * r,
        1 => WORD_LEN - 1 - 2 * r,
        2 => WORD_LEN / 2 + 2 * r,
        _ => WORD_LEN / 2 - 1 - 2 * r,
    }
}

/// SPEC §§3–4: (x_u,y_u) = g^(1024+4096 rev18(u)), embedded in E.
pub fn fibre_point<E: CodeField>(u: FibreIndex) -> Point<E> {
    let g = CM31::new(M31(2), M31(1268011823));
    let value = g.pow(1024 + 4096 * rev18(u) as u64);
    Point {
        x: E::from_m31(value.a),
        y: E::from_m31(value.b),
    }
}
pub fn exact_circle_x<E: CodeField>(u: FibreIndex) -> E {
    fibre_point::<E>(u).x
}
pub fn exact_circle_y<E: CodeField>(u: FibreIndex) -> E {
    fibre_point::<E>(u).y
}

/// SPEC §3: (X_i,Y_i), exactly g^(1024*(2*n(i)+1)).
pub fn stored_point<E: CodeField>(i: InitialIndex) -> Point<E> {
    let Point { x, y } = fibre_point::<E>(parent_index(i));
    match slot_index(i).0 {
        0 => Point { x, y },
        1 => Point { x, y: y.neg() },
        2 => Point {
            x: x.neg(),
            y: y.neg(),
        },
        _ => Point { x: x.neg(), y },
    }
}
/// SPEC §§3–4: X(g^(2048+8192 rev18(u))) = 2*x_u²−1.
pub fn line_node<E: CodeField>(u: FibreIndex) -> E {
    basis::double(exact_circle_x::<E>(u))
}
