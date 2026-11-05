import NIY_ResumeFields
import NID_ReadStepFrame
set_option autoImplicit false
noncomputable section
namespace NIY_ReaderFrames
open Aeneas Aeneas.Std Result AspisR1 AspisR1Stage2
open OraclePortCkptAbi2Unwrap CheckpointBytes3Namespaces

/-- The SAME bounded raw call determines its returned cursor and backing. -/
theorem raw (n : Usize) (r : verifier.Reader) (b : Array U8 n) (out : verifier.Reader)
 (bound : r.at.val+n.val≤r.bytes.val.length)
 (call : CheckpointBytes3Reader.raw n r=ok (b,out)) :
 out.at.val=r.at.val+n.val ∧ out.bytes=r.bytes := by
 obtain ⟨actual,post,run,_,cursor,backing⟩ :=
   raw_panic_unreachable r n (fun _=>fail .panic) bound
 unfold CheckpointBytes3Reader.raw at call
 rw [run] at call
 have same : post=out := congrArg Prod.snd (Result.ok.inj call)
 rw [←same]
 exact ⟨cursor,backing⟩

/-- Inner Checkpoint errors also preserve this exact reader sequencing fact. -/
theorem e (r out : verifier.Reader)
 (value : core.result.Result aspis_core.field.wide_exact.WideExact verifier.Error)
 (bound : r.at.val+32≤r.bytes.val.length)
 (call : CheckpointBytes3Reader.readE r=ok (value,out)) :
 out.at.val=r.at.val+32 ∧ out.bytes=r.bytes := by
 obtain ⟨_,post,_,cursor,backing,run⟩ := CheckpointBytes3Reader.read_e_c5 r bound
 rw [run] at call
 have same : post=out := congrArg Prod.snd (Result.ok.inj call)
 rw [←same]
 exact ⟨cursor,backing⟩
#print axioms raw
#print axioms e
end NIY_ReaderFrames
