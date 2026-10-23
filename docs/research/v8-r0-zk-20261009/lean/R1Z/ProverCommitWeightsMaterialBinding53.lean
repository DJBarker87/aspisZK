import AspisR1ProducerRelease47.WeightsMaterial53
import R1Z.ProverCommitWeights53
import R1Z.ProverCommitMaterialOutput49
/-! Reuse one initialized object across all materialized rows. The source row
Results replace table reads under a symbolic counter induction. -/
set_option autoImplicit false
namespace R1Z.ProverCommitWeightsMaterialBinding53
open Aeneas Aeneas.Std Result AspisR1ProducerRelease47
open ProverCommitPrimitive47 ProverCommitWideOps48 ProverCommitMix48
open ProverCommitWeightsStorage53 (State)

theorem fill_eq (st : State) (raw : Nat → Nat → Old.Q)
    (hrow : ∀ j : Usize, j.val<1024 → weights53.row st j=
      ok (ProverCommitQArray48.array 7#usize (raw j.val)))
    (kp : Array Source 7#usize) (n : Nat) (j : Usize) (left : U16)
    (hl : left.val=n) (bound : j.val+n≤1024) (out : Array Source 1024#usize) :
    weights_material53.fill st kp out j left=
      materialization.fill kp (ProverCommitMaterialFill49.table raw) out j left := by
  induction n generalizing j left out with
  | zero =>
    have hz : left=0#u16 := by scalar_tac
    subst left
    rw [weights_material53.fill,materialization.fill]
    simp only [ite_true]
  | succ n ih =>
    have hn : left≠0#u16 := by scalar_tac
    have hj : j.val<1024 := by omega
    have hdec : (U16.wrapping_sub left 1#u16).val=n := by
      rw [ProverCommitPairCounter47.sub_one left (by omega)];omega
    have hinc : (Usize.wrapping_add j 1#usize).val=j.val+1 :=
      ProverCommitPairCounter47.next_val j (by omega)
    have hb : (Usize.wrapping_add j 1#usize).val+n≤1024 := by rw [hinc];omega
    rw [weights_material53.fill,materialization.fill]
    simp only [hn,if_false,hrow j hj,ProverCommitMaterialFill49.table_index raw j hj,bind_tc_ok,lift]
    have tail : ∀ o, weights_material53.fill st kp o (Usize.wrapping_add j 1#usize)
        (U16.wrapping_sub left 1#u16)=
      materialization.fill kp (ProverCommitMaterialFill49.table raw) o
        (Usize.wrapping_add j 1#usize) (U16.wrapping_sub left 1#u16) :=
      fun o => ih _ _ hdec hb o
    simp only [tail]

theorem all_eq (st : State) (raw : Nat → Nat → Old.Q)
    (hrow : ∀ j : Usize, j.val<1024 → weights53.row st j=
      ok (ProverCommitQArray48.array 7#usize (raw j.val))) (kp : Array Source 7#usize) :
    weights_material53.all st kp=materialization.all kp (ProverCommitMaterialFill49.table raw) := by
  unfold weights_material53.all materialization.all
  exact fill_eq st raw hrow kp 1024 0#usize 1024#u16 rfl (by decide) _

def run (st : State) (x : Source) : Result (Array Source 1024#usize) := do
  let kp ← kappa x
  weights_material53.all st kp

theorem run_eq (st : State) (raw : Nat → Nat → Old.Q)
    (hrow : ∀ j : Usize, j.val<1024 → weights53.row st j=
      ok (ProverCommitQArray48.array 7#usize (raw j.val))) (x : Source) :
    run st x=ProverCommitMaterialOutput49.run x (ProverCommitMaterialFill49.table raw) := by
  simp only [run,ProverCommitMaterialOutput49.run,all_eq st raw hrow]

#print axioms fill_eq
#print axioms all_eq
#print axioms run_eq
end R1Z.ProverCommitWeightsMaterialBinding53
