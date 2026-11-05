import NID_BoundedReaders
set_option autoImplicit false
noncomputable section
namespace NID_ReadStepFrame
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2

theorem next (r out : verifier.Reader)
 (value : core.result.Result aspis_core.field.QM31 verifier.Error)
 (bound : r.at.val+16≤r.bytes.val.length)
 (call : CheckpointBytes3Reader.readK r=ok (value,out)) :
 out.at.val=r.at.val+16 ∧ out.bytes=r.bytes := by
 obtain ⟨b,actual,_,cursor,backing,run⟩ := CheckpointBytes3Reader.read_k_c5 r bound
 rw [run] at call
 have same : actual=out := congrArg Prod.snd (Result.ok.inj call)
 rw [←same]
 exact ⟨cursor,backing⟩

theorem remaining (r out : verifier.Reader) (n : Nat)
 (q : aspis_core.field.QM31)
 (bound : r.at.val+16*(n+1)≤r.bytes.val.length)
 (call : CheckpointBytes3Reader.readK r=ok (.Ok q,out)) :
 out.at.val+16*n≤out.bytes.val.length := by
 obtain ⟨cursor,backing⟩ := next r out (.Ok q) (by omega) call
 rw [cursor,backing]
 omega
#print axioms next
#print axioms remaining
end NID_ReadStepFrame
