import NDO_JGr_BatchInputs
import NDO_JHe_SHARealization
import NDO_JHn_R_JHh_C_Batch

section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_PreBatch
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition
open JGr_Geometry

theorem source (p : verifier.Prepared)
    (input scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (prepare : verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
      JFx_NativeBytes.proof () none input=ok (.Ok p,scratch)) :
    installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=ok (.Ok ()) := by
  rw [JGr_BatchInputs.batch_source p input scratch prepare]
  have run := JHh_C_Batch.native
    (⟨JGn_TerminalIdentified.shaDictionary.coremarkerCopyInst,digest.digest⟩ :
      AspisR1Stage2.aspis_core.digest.Digest32 Unit) ()
  change Op5T_Install.body Port4B_Install.leaves
    (⟨JGn_TerminalIdentified.shaDictionary.coremarkerCopyInst,digest.digest⟩ :
      AspisR1Stage2.aspis_core.digest.Digest32 Unit)
    JFx_NativeBytes.proof JFo_Prepared.value.queries JFo_Prepared.value.roots
    JGe_View.folded 0#usize ()=ok (.Ok ()) at run
  rw [run]
  rfl
#print axioms source

theorem inhabited :
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) (g : verifier.QueryGeometry),
      verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      p.queries=JFq_Queries.value ∧ installed.op20 .S2=ok (.Ok initial) ∧
      installed.op18 initial.weights.deref=ok (.Ok pending) ∧
      installed.op19 p.queries 0#usize 10#usize=ok (.Ok g) ∧
      JGp_Loop.Meaning (Tx1Q_Carriers.geometry g) ∧
      installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=ok (.Ok ()) := by
  obtain ⟨p,scratch,initial,pending,g,prepare,queries,init,weights,geometry,meaning,_reach⟩ := JGr_Geometry.inhabited
  exact ⟨p,scratch,initial,pending,g,prepare,queries,init,weights,geometry,meaning,source p _ scratch prepare⟩
#print axioms inhabited
end AspisR1.JHh_C_PreBatch
end
end
section
variable [sha : AspisR1.JHe_SHARealization]
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHh_C_BatchFrontier
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

/-- Closed retained-byte prefix, with roots and the actual entry equation
kept on the SAME prepare/initial/pending/geometry tuple. -/
theorem inhabited :
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial : verifier.Accumulator) (pending : verifier.BatchedWeights) (g : verifier.QueryGeometry),
      verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      p.queries=JFq_Queries.value ∧ p.roots=JFo_Prepared.value.roots ∧
      installed.op20 .S2=ok (.Ok initial) ∧ installed.op18 initial.weights.deref=ok (.Ok pending) ∧
      installed.op19 p.queries 0#usize 10#usize=ok (.Ok g) ∧ JGp_Loop.Meaning (Tx1Q_Carriers.geometry g) ∧
      installed.op6 digest JFx_NativeBytes.proof p JGe_View.folded 0#usize ()=ok (.Ok ()) ∧
      verifier.candidate.tx1 installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.publicInput JFx_NativeBytes.proof 10#usize () none=
        Tx1Reachability.afterPrepare installed digest JFx_NativeBytes.publicInput JFx_NativeBytes.proof
          10#usize () none p scratch := by
  obtain ⟨p,scratch,initial,pending,g,prepare,queries,roots,init,pend,geo,meaning,entry⟩ :=
    JGr_PreBatchFixture.inhabited
  exact ⟨p,scratch,initial,pending,g,prepare,queries,roots,init,pend,geo,meaning,
    JHh_C_PreBatch.source p _ scratch prepare,entry⟩
#print axioms inhabited
end AspisR1.JHh_C_BatchFrontier
end
end
