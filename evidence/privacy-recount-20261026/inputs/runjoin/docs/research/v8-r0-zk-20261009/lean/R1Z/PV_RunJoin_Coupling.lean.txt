import R1Z.ProverCommitFuelJoin22
import R1Z.ProverCommitTapeCompletion

/-! Exact marginal construction, conditional on an actual coordinate map.
No native entropy adequacy or coordinate map is supplied by this module. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_Coupling
open R0Z R0Z.JointView R0Z.FsStatement R0Z.FsAbort R0Z.HvzkV R0Z.LawTransport
open R1Z.ProverCommitFuelJoin22

/-- V036 and V037 on ONE carrier. A runtime-to-model coordinate bijection
suffices, but its actual deployed construction remains an obligation. -/
def cp {R M : Type} [Fintype R] [Nonempty R] [Fintype M]
    (coordinates : R ≃ ((M × OracleAnswer) × Tape)) :
    Coupling R ((M × OracleAnswer) × Tape) where
  S := R
  finS := inferInstance
  nonemptyS := inferInstance
  toR := id
  toM := coordinates
  meanR := fun _ => rfl
  meanM := R1Z.CouplingR1PBin.mp_equiv coordinates

theorem real_marginal {R M : Type} [Fintype R] [Nonempty R] [Fintype M]
    (coordinates : R ≃ ((M × OracleAnswer) × Tape)) (f : R → ℚ) :
    mean (fun s => f ((cp coordinates).toR s)) = mean f :=
  (cp coordinates).meanR f

theorem model_marginal {R M : Type} [Fintype R] [Nonempty R] [Fintype M]
    (coordinates : R ≃ ((M × OracleAnswer) × Tape))
    (f : ((M × OracleAnswer) × Tape) → ℚ) :
    mean (fun s => f ((cp coordinates).toM s)) = mean f :=
  (cp coordinates).meanM f

/-- Completion's existing bijection preserves the WHOLE tape law. This is
not a claim that a native getrandom tape has that law. -/
theorem completed_tape_mean {K : Type} [Field K] [Fintype K] (F : Subfield K)
    (f : R0Z.JointView.Tape K F → ℚ) :
    mean (fun s : ProverCommitTapeCompletion.SourceTape K F ×
        ProverCommitTapeCompletion.Padding K F =>
      f (ProverCommitTapeCompletion.complete s.1 s.2)) = mean f :=
  R1Z.CouplingR1PBin.mp_equiv ProverCommitTapeCompletion.completionEquiv f

/-- A common product carrier gives the real marginal outright. Only the
model push-forward law is a supplied Prop, to be exposed as V037 by consumers.
Padding and the map remain data; this is not a deployed construction. -/
def projection_cp {R M P : Type} [Fintype R] [Nonempty R]
    [Fintype M] [Fintype P] [Nonempty P]
    (toModel : R × P → ((M × OracleAnswer) × Tape))
    (uniform : ∀ f : ((M × OracleAnswer) × Tape) → ℚ,
      mean (fun s => f (toModel s)) = mean f) :
    Coupling R ((M × OracleAnswer) × Tape) where
  S := R × P
  finS := inferInstance
  nonemptyS := inferInstance
  toR := Prod.fst
  toM := toModel
  meanR := R1Z.CouplingR1PBin.mp_fst
  meanM := uniform

#print axioms projection_cp

#print axioms cp
#print axioms real_marginal
#print axioms model_marginal
#print axioms completed_tape_mean
end R1Z.PV_RunJoin_Coupling
