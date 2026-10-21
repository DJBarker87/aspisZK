import R1Z.PrivacyR1HeadlineAcct
/-! Model-level obstructions to deleting the D80 wire premises.
No tape or finite commitment universe is evaluated. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1HeadlineWire
open R0P R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.FsGood R0Z.HvzkV R0Z.HvzkS R0Z.RefPayload
  R1Z.Batched R1Z.PredicateR1 R1Z.MaskImageVR1 R1Z.PoleMassR1 R1Z.ModelsVR1 R1Z.SimulatorR1
  R1Z.GamesR1 R1Z.Sem1UniformR1 R1Z.GamesR1PBin R1Z.CouplingR1PBin R1Z.EventsR1PBin R1Z.FinalR1PBin
  R1Z.CommitReadsR1 R1Z.PremisesR1PBin R1Z.QueryScanPrivacyFinal R1Z.LayoutR1PBin
attribute [local instance] Classical.propDecidable
open R1Z.ProverCommitTapeCompletion
open R1Z.PhaseProtocolInstanceBin R1Z.PrivacyR1Final R1Z.QueryScanHistorySplit
open R1Z.PrivacyR1Headline
local notation "K" => PrivacyR1AcctBasis.K
local notation "F" => PrivacyR1AcctBasis.F
local notation "B" => PrivacyR1AcctBasis.basis
local notation "hB" => PrivacyR1AcctBasis.packing_laws
local notation "L₁" => PrivacyR1AcctModel.L₁
local notation "L₂" => PrivacyR1AcctModel.L₂
attribute [local irreducible] ProverCommitSourceDecoder.L₁ ProverCommitSourceDecoder.L₂
variable {CommitHandle Aux : Type}
variable (template : R1Wire K CommitHandle Aux)
    (log : (RIdx → OracleAnswer) → (Fin 3 → OracleAnswer) →
      View K CommitHandle Aux R1Bat → Challenges K → List (List UInt8 × OracleAnswer))
local notation "base" => PrivacyR1AcctModel.base template log
variable (h : HonestProver K)
    (outputs : Statement K CommitHandle → Challenges K → Aux)
    (x : Statement K CommitHandle)
variable (decode : (Fin PrivacyR1AcctModel.E₁ → OracleAnswer) →
    (Fin PrivacyR1AcctModel.E₂ → OracleAnswer) → Option (Tape K F))
    (fib : Challenges K → Fin 3 → Finset Fib)
    (opens : Challenges K → List (Fin 3 ⊕ RIdx))
local notation "seed" => PrivacyR1AcctModel.seed
  (R1Z.PhaseLocalityBin.R1PhaseWire.toWire (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x)) decode fib opens

/-- The constructed wire retains the independently supplied verifier log. -/
theorem log_retained (cm : RIdx → OracleAnswer) (roots : Fin 3 → OracleAnswer)
    (v : View K CommitHandle Aux R1Bat) (ch : Challenges K) :
    (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x).toWire.comLog cm roots v ch =
      log cm roots v ch := rfl

/-- The phase construction does not normalize or complete the opening list. -/
theorem openings_retained (ch : Challenges K) :
    (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x seed).toProver.openList ch =
      opens ch := rfl

/-- Empty opening data is admissible model data, but cannot cover even a root.
This disproves unconditional D80 batches at the accounting specialization. -/
theorem empty_openings_no_batches (ch : Challenges K) :
    ¬ Nonempty (RWireBatches
      (wire base (List.length (R1Wire.pubBytes base x)) h B outputs x).toWire
      (prover base (List.length (R1Wire.pubBytes base x)) h B outputs x
        (PrivacyR1AcctModel.seed _ decode fib (fun _ => []))).toProver) := by
  rintro ⟨batch⟩
  have hc := (wire_batches _ _ batch).covers ch (Sum.inl 0)
  have hm := hc.mpr (show LayoutR1PBin.openedQ _ (Sum.inl 0) from trivial)
  change (Sum.inl (0 : Fin 3)) ∈ ([] : List (Fin 3 ⊕ RIdx)) at hm
  exact List.not_mem_nil hm

/-- An empty verifier log and a singleton root opening are both legal model
inputs. Their ordered-log equation fails for every tape and challenge. -/
theorem empty_log_singleton_opening
    (w : h.Instance) (sec : SecP) (d : OracleAnswer) (τ : Tape K F)
    (roots : Fin 3 → OracleAnswer) (rest : RIdx → OracleAnswer) (ch : Challenges K) :
    let b := PrivacyR1AcctModel.base template (fun _ _ _ _ => [])
    let W := (wire b ((b.pubBytes x).length) h B outputs x).toWire
    let P := (prover b ((b.pubBytes x).length) h B outputs x
      (PrivacyR1AcctModel.seed W decode fib (fun _ => [Sum.inl 0]))).toProver
    W.comLog rest roots (view h B outputs x w ch τ) ch ≠
      (P.openList ch).map (fun c =>
        (gram (W.pubBytes x) W.vtag (P.leafVal h w x τ ch) sec d rest
          (cposOf (E₁ := P.E₁) (E₂ := P.E₂) c), ansC roots rest c)) := by
  dsimp only
  change ([] : List (List UInt8 × OracleAnswer)) ≠ [_]
  intro he
  cases he

#print axioms log_retained
#print axioms openings_retained
#print axioms empty_openings_no_batches
#print axioms empty_log_singleton_opening
end R1Z.PrivacyR1HeadlineWire
