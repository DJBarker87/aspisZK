import R1Z.CausalTreeOrderBin
import Mathlib.Data.Finset.Sort

/-! Symbolic phase schedule. The finite-order isomorphism is used only through
its order laws: no concrete list of positions or tree recurrence is reduced. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PhaseScheduleBin
open R1Z.GamesR1PBin R1Z.LayoutR1PBin R1Z.TranscriptR1

def treeBase (T : Fin 3) : ℕ := if T.val = 0 then 1 else if T.val = 1 then 27 else 131

def transcriptStage : TRead → ℕ
  | .init => 26
  | .absS i => if i.val < 2 then 27 + 3 * i.val else 52 + 3 * (i.val - 2)
  | .sqS i => if i.val < 2 then 28 + 3 * i.val else 53 + 3 * (i.val - 2)
  | .advS i => if i.val < 2 then 29 + 3 * i.val else 54 + 3 * (i.val - 2)
  | .reseed => 127
  | .absO i => if i.val < 3 then 128 + 3 * i.val else 156
  | .sqO i => if i.val < 3 then 129 + 3 * i.val else 157
  | .advO i => if i.val < 3 then 130 + 3 * i.val else 158
  | .absQ => 159
  | .qb k => 160 + 2 * k.val
  | .qa k => 161 + 2 * k.val
  | .absR => 176
  | .sqR => 177
  | .advR => 178

def restStage : RIdx → ℕ
  | .inl b => b.val
  | .inr (.inl i) => 2 + i.val
  | .inr (.inr (.inl _)) => 6
  | .inr (.inr (.inr (.inl (T, _)))) => treeBase T + 6
  | .inr (.inr (.inr (.inr (T, n)))) => treeBase T + 7 + n.1.val

def stage {E₁ E₂ : ℕ} : Pos1 E₁ E₂ → ℕ
  | .inl j => transcriptStage j
  | .inr (.inl T) => treeBase T + 24
  | .inr (.inr (.inl _)) => 5
  | .inr (.inr (.inr q)) => restStage q

/-- Separate type prevents the schedule order leaking into other interfaces. -/
def Scheduled (E₁ E₂ : ℕ) := Pos1 E₁ E₂
instance (E₁ E₂ : ℕ) : Fintype (Scheduled E₁ E₂) := inferInstanceAs (Fintype (Pos1 E₁ E₂))

def key {E₁ E₂ : ℕ} (p : Scheduled E₁ E₂) : ℕ ×ₗ ℕ :=
  toLex (stage p, (Fintype.equivFin (Pos1 E₁ E₂) p).val)

theorem key_injective {E₁ E₂ : ℕ} : Function.Injective (@key E₁ E₂) := by
  intro p q h
  apply (Fintype.equivFin (Pos1 E₁ E₂)).injective
  apply Fin.ext
  exact congrArg (fun x : ℕ ×ₗ ℕ => (ofLex x).2) h

instance (E₁ E₂ : ℕ) : LinearOrder (Scheduled E₁ E₂) :=
  LinearOrder.lift' key key_injective

def orderIso (E₁ E₂ : ℕ) : Fin (Fintype.card (Pos1 E₁ E₂)) ≃o Scheduled E₁ E₂ :=
  Fintype.orderIsoFinOfCardEq (Scheduled E₁ E₂) rfl

def ord (E₁ E₂ : ℕ) : Fin (Fintype.card (Pos1 E₁ E₂)) ≃ Pos1 E₁ E₂ :=
  (orderIso E₁ E₂).toEquiv

theorem stage_before {E₁ E₂ : ℕ} (p q : Pos1 E₁ E₂) (h : stage p < stage q) :
    (ord E₁ E₂).symm p < (ord E₁ E₂).symm q := by
  apply (orderIso E₁ E₂).symm.strictMono
  show key p < key q
  exact Prod.Lex.left _ _ h

theorem child_before_parent (T : Fin 3) (n : NodeIdx) (j : Fin 2) :
    restStage (childQ T n j) < restStage (qNode T n) := by
  have h := CausalTreeOrderBin.child_before_parent T n j
  rcases n with ⟨⟨d, hd⟩, i⟩
  cases d with
  | zero => simp [childQ, restStage, qLeaf, qNode]
  | succ d => simp [childQ, restStage, qNode]

theorem root_children (T : Fin 3) (j : Fin 2) :
    restStage (rootChild T j) < treeBase T + 24 := by
  simp [rootChild, restStage, qNode]

#print axioms key_injective
#print axioms stage_before
#print axioms child_before_parent
#print axioms root_children
end R1Z.PhaseScheduleBin
