import R1Z.PV_RDCD3_FieldSource
namespace R1Z.PV_RDCD3_Total
set_option autoImplicit false
open Aeneas Aeneas.Std Result
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev Q := ProverRwFull.aspis_core.field.QM31

def Total {A : Type} (r : Result A) : Prop := ∃ a, r = ok a

theorem ok_total {A : Type} (a : A) : Total (ok a) := ⟨a,rfl⟩
theorem bind_total {A B : Type} {r : Result A} {f : A → Result B}
    (hr : Total r) (hf : ∀ a, Total (f a)) : Total (r >>= f) := by
  obtain ⟨a,ha⟩ := hr
  rw [ha]
  exact hf a

def mapResult {A B : Type} (f : A → B) : Result A → Result B
  | ok a => ok (f a)
  | fail e => fail e
  | div => div

theorem mapped_total {A B : Type} (f : A → B) (r : Result A) (hr : Total r) :
    Total (mapResult f r) := by
  obtain ⟨a,ha⟩ := hr
  exact ⟨f a,by rw [ha]; rfl⟩
#print axioms ok_total
#print axioms bind_total
#print axioms mapped_total
end R1Z.PV_RDCD3_Total
