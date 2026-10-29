import R1Z.PV_OWNI_Scanner
import R1Z.PV_OWNI_DensePrune
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_OWNJ_DecodeFold
open PV_OWNI_RawOps
attribute [local irreducible] PV_B2_FieldValue.aspis_core.field.QM31.add
 PV_B2_FieldValue.aspis_core.field.QM31.mul PV_B2_FieldValue.aspis_core.field.QM31.sub
variable {K : Type} [Field K]

/-- Canonicality is concrete, not an assumed image of the desired result. -/
def Canon (q : Q) : Prop :=
 q.c0.a.val < 2147483647 ∧ q.c0.b.val < 2147483647 ∧
 q.c1.a.val < 2147483647 ∧ q.c1.b.val < 2147483647

/-- Explicit stage obligations. No theorem here supplies this instance. -/
structure Decoder (decode : Q → K) : Prop where
 zero_eq : decode zero = 0
 one_eq : decode one = 1
 zero_canon : Canon zero
 one_canon : Canon one
 add : ∀ x y, Canon x → Canon y →
  Canon (valueAdd x y) ∧ decode (valueAdd x y) = decode x + decode y
 mul : ∀ x y, Canon x → Canon y →
  Canon (valueMul x y) ∧ decode (valueMul x y) = decode x * decode y
 sub : ∀ x, Canon x →
  Canon (valueSub one x) ∧ decode (valueSub one x) = 1 - decode x

theorem fold (decode : Q → K) (D : Decoder decode) (column : List Q)
 (entries : List (Nat × Q)) (initial : Q) (hi : Canon initial)
 (hc : ∀ e ∈ entries, Canon e.2 ∧ Canon (column[e.1]?.getD zero)) :
 Canon (entries.foldl (PV_OWNI_RawFold.term column) initial) ∧
 decode (entries.foldl (PV_OWNI_RawFold.term column) initial) =
 entries.foldl (fun sum e => sum + decode e.2 * decode (column[e.1]?.getD zero))
  (decode initial) := by
 induction entries generalizing initial with
 | nil => exact ⟨hi,rfl⟩
 | cons x xs ih =>
  obtain ⟨hx,hv⟩ := hc x (by simp)
  obtain ⟨hp,hdp⟩ := D.mul _ _ hx hv
  obtain ⟨ha,hda⟩ := D.add _ _ hi hp
  have hrest := ih (PV_OWNI_RawFold.term column initial x) ha
   (fun e he => hc e (by simp only [List.mem_cons]; exact Or.inr he))
  constructor
  · exact hrest.1
  · simp only [List.foldl_cons]
    rw [hrest.2]
    change xs.foldl _ (decode (valueAdd initial (valueMul x.2 _))) = _
    rw [hda,hdp]

#print axioms fold
end R1Z.PV_OWNJ_DecodeFold
