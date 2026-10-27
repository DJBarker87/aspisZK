import R1Z.PV_RunJoin_EncodingSupport
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ErrorViewObstruction
open R0P R0Z R0Z.JointView R0Z.FsStatement
open R1Z.GamesR1 R1Z.GamesR1PBin
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
variable {CommitHandle Aux : Type}
variable (W : R1Wire K CommitHandle Aux) (Pr : R1ProverP K CommitHandle Aux F W)
    (N : Nat) (hN : 0 < N) (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (adv : R1Adv K CommitHandle Aux) (x : Statement K CommitHandle) (w : h.Instance)
    (r : W.Tab × (Fin N → SecP)) (k : Fin N)
    (selected : FsAbort.firstGood
      (fun o : AttemptOut K CommitHandle Aux => P o.ch ∧ Vp h o.ch w ∧ o.exh = false)
      (realOut W Pr h B outputs x w (W.look r.1) r.2) = some k)

local notation "source" => ProverCommitReencode16.experiment W Pr N hN P Vp
  ProverCommitReencode16.encode

include selected

/-- The exact reencoded source used at the endpoint retains a nonempty log on
its actual firstGood/some branch, for every complete observer. -/
theorem reencoded_success_log_nonempty :
    ((source).real h B outputs adv x w r).observerOracle ≠ [] := by
  change ProverCommitReencode16.encode _
    (realGameP W Pr N P Vp h B outputs
      (ProverCommitReencode16.observer ProverCommitReencode16.encode adv) x w r).observerOracle ≠ []
  apply PV_RunJoin_EncodingSupport.encode_nonempty
  exact PV_RunJoin_EncodingSupport.real_success_log_nonempty W Pr N P Vp h B outputs
    (ProverCommitReencode16.observer ProverCommitReencode16.encode adv) x w r k selected

/-- Necessary failure-path check for V038. A truthful empty-log early native
failure cannot agree with a source-success coin. To obtain a full endpoint
counterexample one must ALSO produce such a concrete shared coin outside the
UNCHANGED bad event and a native observer decoder. Neither is assumed solved. -/
theorem empty_native_log_disagrees (native : ROMView K CommitHandle Aux R1Z.Batched.R1Bat)
    (empty_log : native.observerOracle = []) :
    native.observerOracle ≠ ((source).real h B outputs adv x w r).observerOracle := by
  rw [empty_log]
  exact Ne.symm (reencoded_success_log_nonempty W Pr N hN P Vp h B outputs adv x w r k selected)

#print axioms reencoded_success_log_nonempty
#print axioms empty_native_log_disagrees
end R1Z.PV_RunJoin_ErrorViewObstruction
