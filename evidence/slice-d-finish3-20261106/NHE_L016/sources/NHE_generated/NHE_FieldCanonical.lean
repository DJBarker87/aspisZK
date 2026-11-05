import NHE_FieldPort
set_option autoImplicit false
namespace NHE_FieldCanonical
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

theorem carrier (x : NE) :
 AspisR1CurrentWide.Proof.CanonicalFinish (SAG_DotAdapter.toFinishE (FIo_Install.fromE x)) ↔ canonE x := by
 rfl

theorem success (bytes : Slice U8) (i : Usize) (small : i.val<64) (x : NE)
 (read : FIo_Native.weights.field bytes i=ok x) : canonE x := by
 have run := (NHE_FieldPort.adopted bytes i small).symm
 rw [read] at run
 change FIn_Primitives.field bytes i=ok (FIo_Install.fromE x) at run
 unfold FIn_Primitives.field at run
 obtain ⟨finished,hf,rest⟩ := Port3_PushFrame.bind_success _ _ _ run
 have same := congrArg SAG_DotAdapter.toFinishE (Result.ok.inj rest)
 rw [SAG_DotAdapter.roundtrip_finishE] at same
 have hc := AspisR1CurrentWide.Proof.finishField_success_canonical bytes i finished hf
 rw [same] at hc
 exact (carrier x).mp hc

#print axioms carrier
#print axioms success
end NHE_FieldCanonical
