import JHl_KnownFields
import JHl_ClaimKappa
import JHl_ClaimReached
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHl_NonVacuity
open Aeneas Aeneas.Std Result AspisR1CurrentCaller
open InstalledPreparation FirstComposition JGr_Geometry

theorem source :
    ∃ (p : verifier.Prepared) (scratch : Array aspis_core.field.wide_exact.WideExact 29#usize)
      (initial out : verifier.Accumulator) (pending after : verifier.BatchedWeights)
      (g : verifier.QueryGeometry) (flushed : Slice aspis_core.field.QM31),
      verifier.candidate.prepare installed digest (toCurrentPublic JFs_PublicSerialization.value)
        JFx_NativeBytes.proof () none (Array.repeat 29#usize JGp_TX1Initial.zero)=ok (.Ok p,scratch) ∧
      installed.op20 .S2=ok (.Ok initial) ∧ installed.op18 initial.weights.deref=ok (.Ok pending) ∧
      installed.op19 p.queries 0#usize 10#usize=ok (.Ok g) ∧
      installed.op7 JFx_NativeBytes.proof p initial scratch none g pending 10#usize=ok (.Ok (out,after)) ∧
      installed.op17 after out.weights.deref=ok flushed ∧
      JHl_KnownFields.Fields p {out with weights:=⟨flushed.val,flushed.property⟩} ∧
      ∀ n : Fin 7, CheckpointBytes5Output.ofE (Tx1Q_Carriers.e p.kappa)^n.val=JHl_ClaimKappa.value n.val := by
  obtain ⟨p,scratch,initial,out,pending,after,g,flushed,prepare,init,pend,geo,query,flush⟩ :=
    JHc_InstalledQuery.inhabited
  exact ⟨p,scratch,initial,out,pending,after,g,flushed,prepare,init,pend,geo,query,flush,
    JHl_KnownFields.source p _ scratch initial out pending after g flushed prepare init pend geo query flush,
    JHl_ClaimKappa.source p _ scratch prepare⟩
#print axioms source
end AspisR1.JHl_NonVacuity
end
