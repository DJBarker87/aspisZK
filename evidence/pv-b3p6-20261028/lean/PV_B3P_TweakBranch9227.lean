import PV_B3P_P227_09
namespace PV_B3P_Binding9227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
attribute [local irreducible] aspis_core.field.M31.add

theorem tweak_false_branch9 (value : U32) (lane : Usize) :
    reference_terminal.tweak227 value false lane = .ok value := by
  simp only [reference_terminal.tweak227]

theorem tweak_true_branch9 (value : U32) (lane : Usize)
    (h : Usize.wrapping_add lane 1#usize = aspis_statement.poseidon2.DIGEST_ELEMS) :
    reference_terminal.tweak227 value true lane =
      aspis_core.field.M31.add value aspis_statement.poseidon2.MERKLE_NODE_COMPRESSION_V3_TWEAK := by
  simp only [reference_terminal.tweak227,lift,bind_tc_ok,h,↓reduceIte]

#print axioms tweak_false_branch9
#print axioms tweak_true_branch9
end PV_B3P_Binding9227
