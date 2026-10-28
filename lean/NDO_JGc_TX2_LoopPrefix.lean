import NDO_JGc_TX2_LoopStep
import NDO_JFz_TX2_AccumulationChain
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGc_TX2_LoopPrefix
open Aeneas Aeneas.Std Result AspisR1Stage2 Port3_NativeQueryBody

def loop {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C)
    (seed : Ops) (a : verifier.Accumulator) (b : verifier.BatchedWeights) :=
  verifier.candidate.query_loop (JGc_TX2_QueryDictionary.ops seed)
    JFx_NativeBytes.proof JFo_Prepared.value a JFr_TX2_Powers.value none
    (JFv_TX2_Geometry.value err geometrySeed) b 22#usize

theorem source {C : Type} (err : C) (geometrySeed : Port3_NativeGeometryBody.Ops C)
    (seed : Ops) (n : Nat) (bound : n≤12) (a : verifier.Accumulator) (b : verifier.BatchedWeights)
    (run : JFz_TX2_AccumulationChain.updates (JGc_TX2_QueryDictionary.input seed) n=ok (a,b)) :
    loop err geometrySeed seed JFo_Prepared.accumulator JFo_Pending.value=
      loop err geometrySeed seed a b := by
  induction n generalizing a b with
  | zero =>
    have same : (JFo_Prepared.accumulator,JFo_Pending.value)=(a,b) := Result.ok.inj run
    cases same
    rfl
  | succ n ih =>
    obtain ⟨prev,pending,hr,inv⟩ := JFz_TX2_AccumulationChain.source err geometrySeed
      (JGc_TX2_QueryDictionary.input seed) n (by omega)
    obtain ⟨state,hs,hi⟩ := JFz_TX2_ChainStep.source err geometrySeed
      (JGc_TX2_QueryDictionary.input seed) n (by omega) (prev,pending) inv
    have total : JFz_TX2_AccumulationChain.updates (JGc_TX2_QueryDictionary.input seed) (n+1)=ok state := by
      change (do let pair ← JFz_TX2_AccumulationChain.updates (JGc_TX2_QueryDictionary.input seed) n
                 JFz_TX2_ChainStep.transition (JGc_TX2_QueryDictionary.input seed) n pair)=ok state
      rw [hr,bind_tc_ok,hs]
    have same : state=(a,b) := Result.ok.inj (total.symm.trans run)
    subst state
    have next : prev.next=JFv_TX2_GeometryReads.cursor (JFz_TX2_ChainStep.query n) := by
      apply UScalar.eq_of_val_eq
      change prev.next.val=10+n%12
      rw [Nat.mod_eq_of_lt (by omega)]
      exact inv.2.1
    have call := JGc_TX2_QueryStep.source err geometrySeed seed (JFz_TX2_ChainStep.query n)
      prev a pending b next hs
    exact (ih (by omega) prev pending hr).trans
      (JGc_TX2_LoopStep.source _ _ _ _ _ _ _ _ _ _ (by change prev.next.val<22;have:=inv.2.1;omega) call)
#print axioms source
end AspisR1.JGc_TX2_LoopPrefix
end
