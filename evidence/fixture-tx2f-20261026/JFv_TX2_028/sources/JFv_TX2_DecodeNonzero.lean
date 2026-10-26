import SAQ_Inverse
set_option autoImplicit false
namespace AspisR1.JFv_TX2_DecodeNonzero
open Aeneas Aeneas.Std

theorem source (x : U32) (canonical : x.val<2147483647) (raw : x≠0#u32) :
    S7JoinBasisMachine.decode x≠0 := by
  intro zero
  have same : x=0#u32 := SAQ_Inverse.canonical_injective x 0#u32 canonical (by decide) zero
  exact raw same
#print axioms source
end AspisR1.JFv_TX2_DecodeNonzero
