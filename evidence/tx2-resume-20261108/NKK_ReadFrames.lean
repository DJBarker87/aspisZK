import NJZ_Readers
set_option autoImplicit false
noncomputable section
namespace NKK_ReadFrames
open Aeneas Aeneas.Std Result AspisR1 NID_ResumeEmission
abbrev Reader := verifier.Reader

def Frame (width : Nat) (before after : Reader) : Prop :=
 after.bytes=before.bytes ∧ after.at.val=before.at.val+width

/-- The full Reader post-state is retained even when the K decoder returns
Rust Err. Only an entered raw bound is required; no canonicality premise. -/
theorem k (r out : Reader)
 (reply : core.result.Result aspis_core.field.QM31 verifier.Error)
 (bound : r.at.val+16≤r.bytes.val.length)
 (returned : NIL_FreshOps.readK r=ok (reply,out)) : Frame 16 r out := by
 obtain ⟨b,next,cut,actual⟩:=NJZ_Readers.k_source r bound
 rw [←NJZ_Readers.k_reference r] at returned
 have same := Result.ok.inj (actual.symm.trans returned)
 have output := congrArg Prod.snd same
 dsimp only at output
 rw [←output]
 exact ⟨cut.2.2,cut.2.1⟩

theorem e (r out : Reader)
 (reply : core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error)
 (bound : r.at.val+32≤r.bytes.val.length)
 (returned : NIL_FreshOps.readE r=ok (reply,out)) : Frame 32 r out := by
 obtain ⟨b,next,cut,actual⟩:=NJZ_Readers.e_source r bound
 rw [←NJZ_Readers.e_reference r] at returned
 have same := Result.ok.inj (actual.symm.trans returned)
 have output := congrArg Prod.snd same
 dsimp only at output
 rw [←output]
 exact ⟨cut.2.2,cut.2.1⟩

#print axioms k
#print axioms e
end NKK_ReadFrames
