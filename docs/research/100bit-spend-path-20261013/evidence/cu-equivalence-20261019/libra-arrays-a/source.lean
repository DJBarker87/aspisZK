import CuSavingsLibraSourcePrepare
set_option autoImplicit false
namespace AspisR1.CuSavingsLibraSourceArrays
open Aeneas Aeneas.Std Result AspisR1Libra
open CuSavingsLibraSourceModel CuSavingsLibraSourceControl CuSavingsLibraSourceFactored
variable {R S : Type} [CommSemiring R] [CommSemiring S] [Shared]
variable (A : Arithmetic R S)

def Canonical (weights : Points) : Prop :=
  ∀ i, i<4 → A.canonicalE (lookup weights field.wide_exact.WideExact.ZERO i)
def decoded (weights : Points) (i : Nat) : R :=
  A.decodeE (lookup weights field.wide_exact.WideExact.ZERO i)

theorem update (weights : Points) (i : Usize) (value : E) (hi : i.val<4) :
    Array.update weights i value=.ok (weights.set i value) := by
  have hlen : i.val<weights.val.length := by scalar_tac
  obtain ⟨result,hr,hv⟩ := WP.spec_imp_exists (Array.update_spec weights i value hlen)
  simpa only [hv] using hr

theorem lookup_set (weights : Points) (i : Usize) (hi : i.val<4) (value : E) (j : Nat) :
    lookup (weights.set i value) field.wide_exact.WideExact.ZERO j =
      if j=i.val then value else lookup weights field.wide_exact.WideExact.ZERO j := by
  have hlen : i.val<weights.val.length := by scalar_tac
  simp only [lookup,Array.set_val_eq,List.getD_eq_getElem?_getD]
  by_cases he : i.val=j
  · subst j
    rw [List.getElem?_set_self hlen]
    simp
  · rw [List.getElem?_set_ne he,if_neg (Ne.symm he)]

theorem update_canonical (weights : Points) (i : Usize) (hi : i.val<4) (value : E)
    (hw : Canonical A weights) (hv : A.canonicalE value) :
    Canonical A (weights.set i value) := by
  intro j hj
  rw [lookup_set weights i hi value j]
  split
  · exact hv
  · exact hw j hj

theorem decoded_set (weights : Points) (i : Usize) (hi : i.val<4) (value : E) (j : Nat) :
    decoded A (weights.set i value) j =
      if j=i.val then A.decodeE value else decoded A weights j := by
  unfold decoded
  rw [lookup_set weights i hi value j]
  split <;> rfl

#print axioms update
#print axioms lookup_set
#print axioms update_canonical
#print axioms decoded_set
end AspisR1.CuSavingsLibraSourceArrays
