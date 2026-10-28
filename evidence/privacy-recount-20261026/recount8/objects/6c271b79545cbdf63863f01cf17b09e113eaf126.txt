import R1Z.PV_RDCD_Slice194
set_option autoImplicit false
namespace R1Z.PV_RDCD_SliceArrayBinding
open Aeneas Aeneas.Std Result

theorem compare_eq {A B : Type} (p : core.cmp.PartialEq A B) (xy : A × B) :
    PV_RDCD_Slice194.compare p xy = (do
      let b ← p.ne xy.1 xy.2
      ok (decide (¬b=true))) := by
  rcases xy with ⟨a,b⟩
  unfold PV_RDCD_Slice194.compare
  cases h : p.ne a b with
  | ok different => cases different <;> rfl
  | fail e => rfl
  | div => rfl

theorem array_binding {A B : Type} {N : Usize} (p : core.cmp.PartialEq A B)
    (a : Array A N) (b : Array B N) :
    PV_RDCD_Slice194.source a.val b.val p = core.array.equality.PartialEqArray.eq p a b := by
  rw [PV_RDCD_Slice194.source_model]
  have h : PV_RDCD_Slice194.compare p = (fun xy : A × B => do
      let b ← p.ne xy.1 xy.2
      ok (decide (¬b=true))) := funext (compare_eq p)
  rw [h]
  rfl

theorem no_index_failure {A B : Type} {N : Usize} (a : Array A N) (b : Array B N)
    (i : Nat) (hi : i < a.val.length) :
    i < b.val.length ∧ i+1 ≤ N.val := by
  have ha := a.property
  have hb := b.property
  constructor <;> omega
#print axioms compare_eq
#print axioms array_binding
#print axioms no_index_failure
end R1Z.PV_RDCD_SliceArrayBinding
