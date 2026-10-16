import BackgroundAddressMap

/-! Restrict a sampler and its pending queries to their proved address support. -/
set_option autoImplicit false
namespace AspisR1.BackgroundAddressRestriction
open R0C.V3 FS AspisV8PairedCommitment
open AspisV8R19.OracleResampling
open BackgroundAddressMap
variable {I A X C : Type}

def pend (P : I → Prop) : (ps : List (I × Option A)) →
    (∀ q ∈ ps, P q.1) → List ({i // P i} × Option A)
  | [], _ => []
  | q :: ps, h => (⟨q.1,h q (List.mem_cons_self ..)⟩,q.2) ::
      pend P ps (fun q hq => h q (List.mem_cons_of_mem _ hq))

theorem pendMap_pend (P : I → Prop) (ps : List (I × Option A))
    (h : ∀ q ∈ ps, P q.1) : pendMap Subtype.val (pend P ps h) = ps := by
  induction ps with
  | nil => rfl
  | cons q ps ih => simp only [pend, pendMap_cons]; rw [ih]

section Law
variable [DecidableEq I] [Inhabited A] [Fintype A]

theorem blaw_restrict (P : I → Prop) [DecidablePred P]
    (g : X → List A → C) (obs : C → ℚ) (s : BS I A X) (ps : List (I × Option A))
    (hs : AllLabels P s) (hp : ∀ q ∈ ps, P q.1) :
    blaw g obs (restrict P s hs) (pend P ps hp) = blaw g obs s ps := by
  have h := blaw_rename Subtype.val g obs (restrict P s hs) (pend P ps hp)
  rw [rename_restrict, pendMap_pend] at h
  exact h.symm
end Law

#print axioms pendMap_pend
#print axioms blaw_restrict
end AspisR1.BackgroundAddressRestriction
