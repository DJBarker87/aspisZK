import S9FactorArrayEntryV1
import S9ConstructorV3Loop2InnerCanonicalV1
import S9ActualPairInitialWeightsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1S9NativeArrayCanonicalV1
open AspisR1S9ProductionPairCutV1
open AspisR1S9FactorArrayEntryV1
open AspisR1S9ConstructorV3Loop2InnerCanonicalV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Canonical := AspisR1S9ActualPairWideCanonicalV1.Canonical

def ReadsCanonical {N : Usize} (a : Array W N) : Prop :=
  ∀ (i : Usize) (w : W), Array.index_usize a i=.ok w → Canonical w

theorem repeat_canonical (N : Usize) (w : W) (hw : Canonical w) :
    ReadsCanonical (Array.repeat N w) :=
  AspisR1S9ActualPairInitialWeightsV1.repeated_native_reads Canonical N w hw

theorem set_preserves_canonical {N : Usize} (a : Array W N) (i : Usize) (w : W)
    (hi : i.val<N.val) (ha : ReadsCanonical a) (hw : Canonical w) :
    ReadsCanonical (a.set i w) := by
  intro j x hread
  have hj := index_success_bound (a.set i w) j x hread
  have hx := accepted_index_eq_atN (a.set i w) j hj x hread
  rw [atN_set a i j w hi hj] at hx
  by_cases hji : j.val=i.val
  · rw [if_pos hji] at hx
    rw [hx]
    exact hw
  · rw [if_neg hji] at hx
    rw [hx]
    exact ha j (atN a j hj) (index_atN a j hj)

theorem accepted_update_preserves_canonical {N : Usize} (a out : Array W N)
    (i : Usize) (w : W) (hi : i.val<N.val) (ha : ReadsCanonical a) (hw : Canonical w)
    (h : Array.update a i w=.ok out) : ReadsCanonical out := by
  have hout := accepted_update_eq_set a i hi w out h
  rw [hout]
  exact set_preserves_canonical a i w hi ha hw

theorem accepted_mutable_write_preserves_canonical {N : Usize} (a : Array W N)
    (i : Usize) (old w : W) (back : W → Array W N)
    (ha : ReadsCanonical a) (hw : Canonical w)
    (h : Array.index_mut_usize a i=.ok (old,back)) : ReadsCanonical (back w) := by
  have hi := index_mut_bound a i old back h
  have hb := index_mut_back_set a i old back hi h
  rw [hb]
  exact set_preserves_canonical a i w hi ha hw

#print axioms repeat_canonical
#print axioms set_preserves_canonical
#print axioms accepted_update_preserves_canonical
#print axioms accepted_mutable_write_preserves_canonical
end AspisR1S9NativeArrayCanonicalV1
