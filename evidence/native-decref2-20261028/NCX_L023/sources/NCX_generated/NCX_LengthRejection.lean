import NCX_Install
set_option autoImplicit false
namespace NCX_LengthRejection
open Aeneas Aeneas.Std Result

theorem registry (b : Slice U8) (length : b.val.length ≠ 256) :
    NCX_Reference.decode_verifier_registry_v2 b=ok (.Err .WrongLength) := by
  have h : Slice.len b ≠ (256#usize : Usize) := by
    intro eq
    have hv:=congrArg UScalar.val eq
    exact length hv
  have compare : (Slice.len b != 256#usize)=true := bne_iff_ne.mpr h
  simp only [NCX_Reference.decode_verifier_registry_v2,
    NCX_Reference.POOL_V1_VERIFIER_REGISTRY_V2_BYTES,compare,ite_true]
theorem entry (b : Slice U8) (length : b.val.length ≠ 320) :
    NCX_Reference.decode_verifier_registry_entry_v2 b=ok (.Err .WrongLength) := by
  have h : Slice.len b ≠ (320#usize : Usize) := by
    intro eq
    have hv:=congrArg UScalar.val eq
    exact length hv
  have compare : (Slice.len b != 320#usize)=true := bne_iff_ne.mpr h
  simp only [NCX_Reference.decode_verifier_registry_entry_v2,
    NCX_Reference.POOL_V1_VERIFIER_ENTRY_V2_BYTES,compare,ite_true]
#print axioms registry
#print axioms entry
end NCX_LengthRejection
