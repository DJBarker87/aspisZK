import R1Z.ProverCommitSeedEvent19
import R1Z.GamesR1PBin
/-! The adversary-only suffix, including failed-attempt exhaustion, of the
fixed games. Honest verifier recomputations are not adversary query calls. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverCommitObserverQueries19
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV
open R1Z.Batched R1Z.GamesR1 R1Z.GamesR1PBin R1Z.ProverCommitSeedEvent19
attribute [local instance] Classical.propDecidable
variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
  (N : Nat) (hN : 0 < N) (P : Challenges K → Prop)
  (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)

def real (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (adv : R1Adv K CommitHandle Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (r : W.Tab × (Fin N → SecP)) : List Entry :=
  let H := W.look r.1
  let out := realOut W Pr h B outputs x w H r.2
  match firstGood (fun o : AttemptOut K CommitHandle Aux => P o.ch ∧ Vp h o.ch w ∧ o.exh = false) out with
  | none => runLog (adv.prog W.failView []) H W.qmax
  | some k => runLog (adv.prog (out k).view (out k).log) H W.qmax

theorem real_bound (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux) (adv : R1Adv K CommitHandle Aux)
    (x : Statement K CommitHandle) (w : h.Instance) (r : W.Tab × (Fin N → SecP)) :
    (real W Pr N P Vp h B outputs adv x w r).length ≤ W.qmax := by
  unfold real
  dsimp only
  split <;> exact RomObserverBin.runLog_length _ _ _

def ideal (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat)
    (adv : R1Adv K CommitHandle Aux) (x : Statement K CommitHandle)
    (r : (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)) : List Entry :=
  match firstGood (fun c => P (drawW W c)) r.1 with
  | none => runLog (adv.prog W.failView []) (W.look (r.1 ⟨0,hN⟩).2.2.2) W.qmax
  | some k =>
    let v := sim (drawW W (r.1 k)) (r.2 k)
    runLog (adv.prog v (verLog W x v (r.1 k)))
      (progOracle W x v (r.1 k) (r.1 ⟨0,hN⟩).2.2.2) W.qmax

theorem ideal_bound (sim : Challenges K → Tape K F → View K CommitHandle Aux R1Bat)
    (adv : R1Adv K CommitHandle Aux) (x : Statement K CommitHandle)
    (r : (Fin N → R1Coins W.Cm W.Tab) × (Fin N → Tape K F)) :
    (ideal W N hN P sim adv x r).length ≤ W.qmax := by
  unfold ideal
  split <;> exact RomObserverBin.runLog_length _ _ _

#print axioms real_bound
#print axioms ideal_bound
end R1Z.ProverCommitObserverQueries19
