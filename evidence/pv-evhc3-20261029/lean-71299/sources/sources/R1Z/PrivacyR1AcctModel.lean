import R1Z.PrivacyR1AcctBasis

/-! Explicit protocol accounting specialization. The log, opening data and
full-tape decoder remain model data; no execution or decoder law is asserted. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PrivacyR1AcctModel
open R0P R0Z.JointView R0Z.FsStatement
  R1Z.GamesR1 R1Z.GamesR1PBin R1Z.PhaseProtocolInstanceBin
abbrev K := PrivacyR1AcctBasis.K
abbrev F := PrivacyR1AcctBasis.F
abbrev B := PrivacyR1AcctBasis.basis
abbrev L₁ := ProverCommitSourceDecoder.L₁
abbrev L₂ := ProverCommitSourceDecoder.L₂
abbrev E₁ := ProverCommitSourceDecoder.E₁
abbrev E₂ := ProverCommitSourceDecoder.E₂
attribute [local irreducible] ProverCommitSourceDecoder.L₁ ProverCommitSourceDecoder.L₂
variable {CommitHandle Aux : Type}

/-- Choose the retained binary-oracle carrier, leaving its ordered log as data. -/
def base (template : R1Wire K CommitHandle Aux)
    (log : (RIdx → OracleAnswer) → (Fin 3 → OracleAnswer) →
      View K CommitHandle Aux R1Z.Batched.R1Bat → Challenges K →
        List (List UInt8 × OracleAnswer)) : R1Wire K CommitHandle Aux :=
  { template with Cm := RIdx → OracleAnswer
                  finCm := inferInstance
                  neCm := inferInstance
                  comLog := log }

/-- Fixed source sizes. Placeholder address/leaf/order fields are overwritten
by `PhaseProtocolInstanceBin.prover`; the decoder and opening data are retained. -/
def seed (W : R1Wire K CommitHandle Aux)
    (decode : (Fin E₁ → OracleAnswer) → (Fin E₂ → OracleAnswer) → Option (Tape K F))
    (fib : Challenges K → Fin 3 → Finset Fib)
    (opens : Challenges K → List (Fin 3 ⊕ RIdx)) : R1ProverP K CommitHandle Aux F W where
  E₁ := E₁
  E₂ := E₂
  caddr := fun _ _ _ _ _ _ _ _ _ => []
  leafVal := fun _ _ _ _ _ _ _ => []
  tapeOf := decode
  openFib := fib
  openList := opens
  ord := PhaseScheduleBin.ord E₁ E₂

theorem cell_count : R1Z.CommitReadsR1.RCommitCount L₁ L₂ :=
  ProverCommitSourceDecoder.source_counts

theorem stream₁ : 16 * L₁ ≤ E₁ * 8 := ProverCommitSourceDecoder.source_budgets.1
theorem stream₂ : 16 * L₂ ≤ E₂ * 8 := ProverCommitSourceDecoder.source_budgets.2.1
theorem blocks₁ : E₁ ≤ 2 * L₁ := le_rfl
theorem blocks₂ : E₂ ≤ 2 * L₂ := le_rfl

theorem counter₁ : E₁ < 2^64 := by
  have h := cell_count.1
  change L₁ ≤ 45056 at h
  change 2 * L₁ < 2^64
  norm_num at h ⊢
  omega

theorem counter₂ : E₂ < 2^64 := by
  have h := cell_count.2
  change L₂ = 4096 at h
  change 2 * L₂ < 2^64
  norm_num at h ⊢
  omega

def wire_coins (template : R1Wire K CommitHandle Aux) (log)
    (h : HonestProver K) (outputs) (x : Statement K CommitHandle) :
    (wire (base template log) ((template.pubBytes x).length) h B outputs x).toWire.Cm ≃
      (RIdx → OracleAnswer) := Equiv.refl _

#print axioms base
#print axioms seed
#print axioms cell_count
#print axioms stream₁
#print axioms stream₂
#print axioms blocks₁
#print axioms blocks₂
#print axioms counter₁
#print axioms counter₂
#print axioms wire_coins
end R1Z.PrivacyR1AcctModel
