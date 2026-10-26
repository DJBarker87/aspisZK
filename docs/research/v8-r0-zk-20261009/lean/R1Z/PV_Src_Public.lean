import R1Z.BuilderPublicProjection

/-! The actual extracted public calls for both shipped statement variants.
No native equality is used to define the canonical public projection. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Src_Public
open Aeneas Aeneas.Std Result BuilderPublicProjection
open AspisBuilderPublicSource.pool_v1.pair_forest_semantic_terminal

inductive Input where
  | transfer (p : Transfer) (t : Transition)
  | withdrawal (p : Withdrawal) (t : Transition)

def run : Input → Result SemanticPublic
  | .transfer p t => private_public p t
  | .withdrawal p t => withdrawal_public p t

def value : Input → SemanticPublic
  | .transfer p t => ⟨.PrivateTransfer,p.pool,p.deployment_domain,p.anchor_root,p.nullifier,
      p.asset_id,some p.recipient_commitment,p.change_commitment,none,t⟩
  | .withdrawal p t => ⟨.Withdrawal,p.pool,p.deployment_domain,p.anchor_root,p.nullifier,
      p.asset_id,none,p.change_commitment,some p.amount,t⟩

def canonicalPublic : Input → R0P.Public R1J.SpendWitnessMap.F
  | .transfer p t => transferPublic p t
  | .withdrawal p t => withdrawalPublic p t

theorem run_success (i : Input) : run i = ok (value i) := by cases i <;> rfl

/-- Execute the extracted public call. Totality, rather than an admission
premise, proves that the fallback is unreachable. -/
def output (i : Input) : SemanticPublic :=
  R0Z.WriterRefine.okOr (run i) (value i)

theorem output_eq (i : Input) : output i = value i := by
  rw [output,run_success,R0Z.WriterRefine.okOr_ok]

theorem public_eq (i : Input) : semanticPublic (output i) = canonicalPublic i := by
  rw [output_eq]
  cases i <;> rfl

theorem transfer_public_eq (p : Transfer) (t : Transition) (s : SemanticPublic)
    (h : private_public p t = ok s) :
    semanticPublic s = canonicalPublic (.transfer p t) :=
  transfer_success p t s h

theorem withdrawal_public_eq (p : Withdrawal) (t : Transition) (s : SemanticPublic)
    (h : withdrawal_public p t = ok s) :
    semanticPublic s = canonicalPublic (.withdrawal p t) :=
  withdrawal_success p t s h

#print axioms run_success
#print axioms output_eq
#print axioms public_eq
#print axioms transfer_public_eq
#print axioms withdrawal_public_eq
end R1Z.PV_Src_Public
