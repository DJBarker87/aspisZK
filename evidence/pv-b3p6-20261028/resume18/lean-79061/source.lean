import PV_B3P_RawRefTail1550227
import Lean.Elab.Tactic.AsAuxLemma
namespace PV_B3P_Association550227
open Aeneas Aeneas.Std PV_B3P_227 Result PV_B3P_Binding9227
set_option autoImplicit false
attribute [local irreducible] Array.index_usize reference_poseidon.extension_limbs
  reference_poseidon.raw_limb227 U64.wrapping_add U64.wrapping_sub U64.wrapping_mul
  core.convert.num.FromU64U32.from

theorem raw_reference_factor550 (input : Array aspis_core.field.QM31 4#usize) :
    reference_poseidon.external_local_packed_raw input = (do
  let q ← Array.index_usize input 0#usize
  let a ← reference_poseidon.extension_limbs q
  let q1 ← Array.index_usize input 1#usize
  let a1 ← reference_poseidon.extension_limbs q1
  let q2 ← Array.index_usize input 2#usize
  let a2 ← reference_poseidon.extension_limbs q2
  let q3 ← Array.index_usize input 3#usize
  let a3 ← reference_poseidon.extension_limbs q3
  raw_reference_tail0_550 a a1 a2 a3) := by
  unfold reference_poseidon.external_local_packed_raw
  apply bind_equal9
  intro q
  apply bind_equal9
  intro a
  apply bind_equal9
  intro q1
  apply bind_equal9
  intro a1
  apply bind_equal9
  intro q2
  apply bind_equal9
  intro a2
  apply bind_equal9
  intro q3
  apply bind_equal9
  intro a3
  as_aux_lemma =>
    unfold raw_reference_tail0_550
    apply bind_equal9
    intro a4
    apply bind_equal9
    intro i
    apply bind_equal9
    intro a5
    apply bind_equal9
    intro a6
    apply bind_equal9
    intro i1
    apply bind_equal9
    intro b
    apply bind_equal9
    intro a7
    apply bind_equal9
    intro i2
    apply bind_equal9
    intro c
    apply bind_equal9
    intro a8
    apply bind_equal9
    intro i3
    apply bind_equal9
    intro d
    apply bind_equal9
    intro i4
    apply bind_equal9
    intro i5
    apply bind_equal9
    intro a9
    apply bind_equal9
    intro i6
    apply bind_equal9
    intro b1
    apply bind_equal9
    intro i7
    apply bind_equal9
    intro c1
    apply bind_equal9
    intro i8
    as_aux_lemma =>
      apply bind_equal9
      intro d1
      apply bind_equal9
      intro i9
      apply bind_equal9
      intro i10
      apply bind_equal9
      intro a10
      apply bind_equal9
      intro i11
      apply bind_equal9
      intro b2
      apply bind_equal9
      intro i12
      apply bind_equal9
      intro c2
      apply bind_equal9
      intro i13
      apply bind_equal9
      intro d2
      apply bind_equal9
      intro i14
      apply bind_equal9
      intro i15
      apply bind_equal9
      intro a11
      apply bind_equal9
      intro i16
      apply bind_equal9
      intro b3
      apply bind_equal9
      intro i17
      apply bind_equal9
      intro c3
      apply bind_equal9
      intro i18
      apply bind_equal9
      intro d3
      apply bind_equal9
      intro i19
      exact raw_reference_tail1_factor550 a4 a6 a7 a8 i4 i9 i14 i19

#print axioms raw_reference_factor550
end PV_B3P_Association550227
