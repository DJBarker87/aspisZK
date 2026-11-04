import NGC_FinishFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_FinishContents
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- Exact limb values of the SAME pending residue rows, in addition to the
result/frame law. No output vector or successful finish is supplied for free. -/
theorem contents (p : verifier.Prepared) (start finish : Nat)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights)
 (d : NFS_QueryInvariant.Domain p start finish a b) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush b a.weights.deref=ok out ∧
 out.val=(b.raw.val.take 64).map (fun row=>Port3_FlushInstall.fromMutable
  (S8Kani2FinishReferenceJoin.toFinish (S8OwnedP6Finish.modelValue row))) ∧
 out.val.length=64 ∧ ∀ q∈out.val,Port3_FlushInstall.Canonical q := by
 obtain ⟨out,run,len,canonical,_⟩ := NGC_FinishFrame.result_frame p start finish a b d
 have lengths : a.weights.deref.val.length≤b.raw.val.length := by
  change a.weights.val.length≤b.raw.val.length
  rw [d.width,show b.raw.val.length=64 from d.progress.2.1]
 have cells := (Port3_FlushInstall.accepted_contents b a.weights.deref out lengths run).1
 refine ⟨out,run,?_,len,canonical⟩
 change out.val=(b.raw.val.take a.weights.val.length).map (fun row=>Port3_FlushInstall.fromMutable
  (S8Kani2FinishReferenceJoin.toFinish (S8OwnedP6Finish.modelValue row))) at cells
 simpa only [d.width] using cells
#print axioms contents
end AspisR1.NGC_FinishContents
end
