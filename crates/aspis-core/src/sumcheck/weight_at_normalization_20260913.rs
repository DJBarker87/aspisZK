//! Differential checks against the literal pre-normalization method.
//! The preparer generates the included reference directly from the checkout,
//! after validating all replacement spans. This is test evidence, not a proof.
extern crate std;
use super::*;
use alloc::{vec, vec::Vec};
use crate::field::{CM31, M31, QM31};
use std::panic::{catch_unwind, AssertUnwindSafe};

include!("weight_at_legacy_20260913.inc.rs");

fn q(x: u32) -> QM31 {
    QM31::from_cm31(CM31::from_m31(M31(x % crate::field::P)))
}
fn ext(x: u32) -> QM31 {
    let p = crate::field::P;
    QM31 { c0: CM31::new(M31(x % p), M31(x.wrapping_add(1) % p)),
           c1: CM31::new(M31(x.wrapping_add(3) % p), M31(x.wrapping_add(7) % p)) }
}
fn state(log_len: u32, component: WeightComponent) -> WeightAccumulator {
    WeightAccumulator { log_len, components: vec![component] }
}
fn compare_all(w: &WeightAccumulator) {
    for i in 0..(1u32 << w.log_len) {
        assert_eq!(w.weight_at(i), w.weight_at_before_20260913(i),
            "log={}, index={}", w.log_len, i);
    }
}
fn compare_outcome(w: &WeightAccumulator, i: u32) {
    let old = catch_unwind(AssertUnwindSafe(|| w.weight_at_before_20260913(i)));
    let new = catch_unwind(AssertUnwindSafe(|| w.weight_at(i)));
    match (old, new) {
        (Ok(a), Ok(b)) => assert_eq!(a,b),
        (Err(_), Err(_)) => {},
        _ => panic!("normalization changed success/panic disposition"),
    }
}
#[test]
fn multilinear_all_indices_and_widths() {
    for width in 0..=10 {
        for seed in [0, 1, 17, 991] {
            compare_all(&state(width, WeightComponent::Multilinear {
                scale: ext(seed), point: (0..width).map(|i| ext(seed+13*i)).collect(),
            }));
        }
    }
}
#[test]
fn tensor_all_indices_and_widths() {
    for width in 0..=10 {
        compare_all(&state(width, WeightComponent::Tensor {
            scale: ext(29), factors: (0..width).map(|i| ext(31+17*i)).collect(),
        }));
    }
}
#[test]
fn product_preserves_big_endian_slot_order() {
    for width in 0..=10 {
        compare_all(&state(width, WeightComponent::Product {
            scale: ext(47), pairs: (0..width).map(|i| [ext(53+i),ext(97+3*i)]).collect(),
        }));
    }
}
#[test]
fn empty_factors_return_scale() {
    for component in [
        WeightComponent::Multilinear { scale: ext(79), point: vec![] },
        WeightComponent::Tensor { scale: ext(79), factors: vec![] },
        WeightComponent::Product { scale: ext(79), pairs: vec![] },
    ] {
        let w=state(0,component);
        assert_eq!(w.weight_at(0),ext(79));
        compare_all(&w);
    }
}
#[test]
fn zip_stops_at_shorter_slice_in_both_directions() {
    for log in 0..=8 {
        for left in 0..=4 {
            for right in 0..=4 {
                for halves in [0,1,2,7] {
                    compare_all(&state(log, WeightComponent::LineM31Batch {
                        scales: (0..left).map(|i| ext(101+i)).collect(),
                        xs: (0..right).map(|i| M31(113+i)).collect(),
                        deferred_halvings: halves,
                    }));
                }
            }
        }
    }
}
#[test]
fn untouched_geometric_dense_and_line_variants() {
    for log in 0..=8 {
        compare_all(&state(log, WeightComponent::Geometric { scale: ext(127),base:ext(131) }));
        compare_all(&state(log, WeightComponent::Dense {
            values: (0..(1u32<<log)).map(|i| ext(137+i)).collect(),
        }));
        compare_all(&state(log, WeightComponent::LineM31Tensor { scale:ext(139),x:M31(149) }));
    }
}
#[test]
fn ordinary_grouped_variants() {
    for (rows, log) in [(64usize,10u32),(128usize,11u32)] {
        let row_groups: Vec<u8>=(0..rows).map(|i|(i%3) as u8).collect();
        let group_values: Vec<QM31>=(0..48).map(|i|ext(151+i)).collect();
        let component=if rows==64 {
            WeightComponent::Grouped64x16 { row_groups,group_values,low_width:16 }
        } else {
            WeightComponent::Grouped128x16 { row_groups,group_values,low_width:16 }
        };
        compare_all(&state(log,component));
    }
}
#[test]
fn deferred_binary_all_representations() {
    let rows:Vec<u8>=(0..64).map(|i|(i%3) as u8).collect();
    for log in [10u32,8,6,4,2] {
        let component=if log>=8 {
            WeightComponent::Grouped64x16BinaryDeferred {
                row_groups:rows.clone(), group_masks:vec![0x55aa,0xffff,0x8001],
                first_alpha:if log==8 {Some(ext(173))} else {None},group_values:vec![],
            }
        } else {
            WeightComponent::Grouped64x16BinaryDeferred {
                row_groups:(0..(1u32<<log)).map(|i|(i%3) as u8).collect(),
                group_masks:vec![],first_alpha:None,group_values:vec![ext(179),ext(181),ext(191)],
            }
        };
        compare_all(&state(log,component));
    }
}
#[test]
fn mixtures_preserve_component_summation_order() {
    let mut w=WeightAccumulator::empty(8);
    w.add_multilinear(ext(193),(0..8).map(|i|ext(197+i)).collect()).unwrap();
    w.add_tensor_factors(ext(211),(0..8).map(|i|ext(223+i)).collect()).unwrap();
    w.add_product_pairs(ext(227),(0..8).map(|i|[ext(229+i),ext(233+i)]).collect()).unwrap();
    w.add_line_m31_batch(&[ext(239),ext(241)],&[M31(251),M31(257)]).unwrap();
    w.add_dense((0..256).map(|i|ext(263+i)).collect()).unwrap();
    w.add_geometric(ext(269),ext(271));
    compare_all(&w);
}
#[test]
fn real_round_zero_shape_and_full_observer() {
    let mut w=WeightAccumulator::empty(10);
    for row in 0..3 {
        w.add_multilinear(ext(277+row),(0..10).map(|i|ext(281+i+13*row)).collect()).unwrap();
    }
    w.add_grouped_64x16_binary_masks_deferred(core::array::from_fn(|i|
        (i as u16).wrapping_mul(977)^0x55aa)).unwrap();
    for j in 0..2 {
        w.add_tensor_factors(ext(307+j),(0..10).map(|i|ext(311+i+7*j)).collect()).unwrap();
    }
    w.fold_deferred_relation_arity4(ext(331));
    compare_all(&w);
    let v:[QM31;256]=core::array::from_fn(|i|ext(337+i as u32));
    let old=(0..256).fold(QM31::ZERO,|acc,i|
        acc.add(v[i].mul(w.weight_at_before_20260913(i as u32))));
    assert_eq!(crate::v6_transcript::prequery_dot_256(&w,&v),old);
}
#[test]
fn terminal_dot_agrees_with_old_weight_at() {
    let mut w=WeightAccumulator::empty(2);
    w.add_multilinear(ext(347),vec![ext(349),ext(353)]).unwrap();
    w.add_tensor_factors(ext(359),vec![ext(367),ext(373)]).unwrap();
    w.add_product_pairs(ext(379),vec![[ext(383),ext(389)],[ext(397),ext(401)]]).unwrap();
    w.add_line_m31_batch(&[ext(409),ext(419)],&[M31(421),M31(431)]).unwrap();
    let v=[ext(433),ext(439),ext(443),ext(449)];
    let old=(0..4).fold(QM31::ZERO,|acc,i|
        acc.add(v[i].mul(w.weight_at_before_20260913(i as u32))));
    assert_eq!(w.dot(&v),old);
}
#[test]
fn boundary_field_values_and_zero_masks() {
    let p=crate::field::P;
    for x in [0,1,2,p-2,p-1] {
        compare_all(&state(8,WeightComponent::Multilinear {
            scale:q(x),point:vec![q(x);8],
        }));
        compare_all(&state(8,WeightComponent::Product {
            scale:q(x),pairs:vec![[q(x),q(p-1)];8],
        }));
    }
}
#[test]
fn malformed_private_states_keep_panic_or_value_disposition() {
    let cases=[
        state(8,WeightComponent::Dense{values:vec![]}),
        state(8,WeightComponent::Multilinear{scale:q(1),point:vec![q(1);33]}),
        state(8,WeightComponent::Product{scale:q(1),pairs:vec![[q(1),q(2)];33]}),
        state(8,WeightComponent::Grouped64x16{row_groups:vec![],group_values:vec![],low_width:0}),
        state(8,WeightComponent::Grouped64x16BinaryDeferred{
            row_groups:vec![0;64],group_masks:vec![1],first_alpha:None,group_values:vec![]}),
    ];
    for w in cases { compare_outcome(&w,0); }
}
