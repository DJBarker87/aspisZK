import R1Z.ProverCommitReencode16
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_EncodingSupport
open R0P R0Z R0Z.JointView R0Z.FsStatement
open R1Z.GamesR1 R1Z.GamesR1PBin
local notation "K₀" => PrivacyR1AcctBasis.K

/-- The publication encoder cannot erase an existing oracle log. Its retained
transcript hprefix is nonempty even for malformed logs. This lemma supplies no
native decoder or successful-run assumption. -/
theorem encode_nonempty {CommitHandle Aux : Type}
    (v : View K₀ CommitHandle Aux R1Z.Batched.R1Bat)
    (log : List ProverCommitReencode16.Entry) (nonempty : log ≠ []) :
    ProverCommitReencode16.encode v log ≠ [] := by
  unfold ProverCommitReencode16.encode
  split
  · exact nonempty
  · intro empty
    dsimp only at empty
    have hprefix : log.take TranscriptR1.schedule.length = [] := by
      simp only [List.append_eq_nil_iff] at empty
      exact empty.1.1
    cases log with
    | nil => exact nonempty rfl
    | cons a rest =>
      change (a :: rest).take (Nat.succ _) = [] at hprefix
      simp only [List.take_succ_cons,List.cons_ne_nil] at hprefix

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] {F : Subfield K}

/-- Every model attempt's verifier recomputation contains the init read.
Therefore an accepted model attempt has a nonempty complete oracle log. -/
theorem attempt_log_nonempty (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle) (w : h.Instance)
    (H : List UInt8 → OracleAnswer) (secret : SecP) (digest : OracleAnswer)
    (answers : Pos1 Pr.E₁ Pr.E₂ → OracleAnswer) :
    (attOut W Pr h B outputs x w H secret digest answers).log ≠ [] := by
  change (TranscriptR1.schedule.map _ ++ _) ≠ []
  intro empty
  have hprefix := (List.append_eq_nil_iff.mp empty).1
  have schedule := List.map_eq_nil_iff.mp hprefix
  have member := TranscriptR1.mem_schedule .init
  rw [schedule] at member
  cases member

/-- Exact success branch of the unchanged real model. The claim covers the
complete log, including the adversary suffix; an idle observer does not erase
verifier recomputation. -/
theorem real_success_log_nonempty (W : R1Wire K CommitHandle Aux)
    (Pr : R1ProverP K CommitHandle Aux F W) (N : Nat)
    (P : Challenges K → Prop)
    (Vp : (h : HonestProver K) → Challenges K → h.Instance → Prop)
    (h : HonestProver K) (B : PackBasis F)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (adv : R1Adv K CommitHandle Aux)
    (x : Statement K CommitHandle) (w : h.Instance)
    (r : W.Tab × (Fin N → SecP)) (k : Fin N)
    (selected : R0Z.FsAbort.firstGood
      (fun o : AttemptOut K CommitHandle Aux => P o.ch ∧ Vp h o.ch w ∧ o.exh = false)
      (realOut W Pr h B outputs x w (W.look r.1) r.2) = some k) :
    (realGameP W Pr N P Vp h B outputs adv x w r).observerOracle ≠ [] := by
  unfold realGameP
  dsimp only
  rw [selected]
  intro empty
  have hprefix := (List.append_eq_nil_iff.mp empty).1
  exact attempt_log_nonempty W Pr h B outputs x w (W.look r.1) (r.2 k)
    (W.look r.1 (W.pubBytes x)) _ hprefix

#print axioms encode_nonempty
#print axioms attempt_log_nonempty
#print axioms real_success_log_nonempty
end R1Z.PV_RunJoin_EncodingSupport
