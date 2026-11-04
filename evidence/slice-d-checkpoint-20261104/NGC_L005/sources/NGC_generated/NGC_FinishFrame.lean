import NFS_QueryInvariant
import Port3_FlushInstall
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGC_FinishFrame
open Aeneas Aeneas.Std Result AspisR1Stage2
/-- SAME pending/weights pair. This is a total result/frame law, not an
accepted-finish hypothesis. No residue bound is needed for reduction. -/
theorem result_frame (p : verifier.Prepared) (start finish : Nat)
 (a : verifier.Accumulator) (b : verifier.BatchedWeights)
 (d : NFS_QueryInvariant.Domain p start finish a b) :
 ∃ out : Slice aspis_core.field.QM31,
 Port3_FlushInstall.flush b a.weights.deref=ok out ∧
 out.val.length=64 ∧
 (∀ q∈out.val,Port3_FlushInstall.Canonical q) ∧
 let after : verifier.Accumulator := {a with weights:=⟨out.val,out.property⟩}
 after.rhs=a.rhs ∧ after.power=a.power ∧ after.next=a.next := by
 have raw : b.raw.val.length=64 := d.progress.2.1
 have lengths : a.weights.deref.val.length≤b.raw.val.length := by
  change a.weights.val.length≤b.raw.val.length
  omega
 let out := Port3_FlushInstall.fromSlice
  ⟨(S8JoinFinishExact.output b.raw (Port3_FlushInstall.toWeights a.weights.deref)).val.map
   S8Kani2FinishReferenceJoin.toFinish,
   by simpa using (S8JoinFinishExact.output b.raw (Port3_FlushInstall.toWeights a.weights.deref)).property⟩
 have run : Port3_FlushInstall.flush b a.weights.deref=ok out :=
  Port3_FlushInstall.flush_exact b a.weights.deref lengths
 have len := (Port3_FlushInstall.accepted_contents b a.weights.deref out lengths run).2
 refine ⟨out,run,?_,Port3_FlushInstall.accepted_canonical b a.weights.deref out lengths run,?_⟩
 · exact len.trans d.width
 · exact ⟨rfl,rfl,rfl⟩
#print axioms result_frame
end AspisR1.NGC_FinishFrame
end
