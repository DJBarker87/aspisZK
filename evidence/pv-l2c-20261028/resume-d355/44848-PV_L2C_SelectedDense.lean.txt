import PV_L2C_RowEnumeration
import PV_L2C_PaddingNative
set_option autoImplicit false
namespace PV_L2C_SelectedDense
open Aeneas Aeneas.Std Result
open PV_L2C_NativeQ PV_L2C_QBalance PV_L2C_QFold PV_L2C_PaddingNative
open PV_L2C_ExtractedRows PV_L2C_OwnedBalance PV_L2C_RowEnumeration

theorem filtered_dense {I : Type} (rows : List I) (sel : I → Bool) (value : I → Q)
    (hc : ∀ i∈rows,Canonical (value i)) (s : Q) (hs : Canonical s) :
    foldQ (rows.filterMap (fun i => if sel i then some (value i) else none)) s=
      foldQ (rows.map (fun i => if sel i then value i else zero)) s := by
  induction rows generalizing s with
  | nil => rfl
  | cons i is ih =>
    have ht : ∀ j∈is,Canonical (value j) := fun j hj => hc j (by simp [hj])
    cases h : sel i with
    | false =>
      simp only [List.filterMap_cons,List.map_cons,h,Bool.false_eq_true,if_false,foldQ,
        native_add_zero s hs]
      exact ih ht s hs
    | true =>
      simp only [List.filterMap_cons,List.map_cons,h,if_true,foldQ]
      exact ih ht _ (add_canonical s (value i) hs (hc i (by simp)))
#print axioms filtered_dense

theorem index_injective : Function.Injective index := by
  intro i j h
  apply Fin.ext
  have he := congrArg UScalar.val h
  simpa only [index_val] using he
#print axioms index_injective

/-- Exactly the excluded finite sum, with the extracted traversal order. -/
theorem selected_sum (table : Fin 1024 → Q) (active : Fin 1024 → Bool) (d : Fin 1024)
    (hc : ∀ i,Canonical (table i)) :
    foldQ (selected table active (index d) rows) zero=excluded active d table := by
  unfold selected
  rw [filtered_dense rows _ _ (by
    intro r hr
    have hb := rows_bounded r hr
    simp only [lookup,dif_pos hb]
    exact hc _) zero zero_canonical,enumeration,List.map_ofFn]
  change foldQ (List.ofFn (fun i =>
    if (!flag active (index i)) && (index i != index d) then lookup table (index i) else zero)) zero=
      foldQ (List.ofFn (inactiveTable active (without d table))) zero
  apply congrArg (fun values : List Q => foldQ values zero)
  apply congrArg (fun f : Fin 1024 → Q => List.ofFn f)
  funext i
  have hb : (index i).val<1024 := by rw [index_val];exact i.isLt
  have he : (index i=index d)↔i=d := index_injective.eq_iff
  have hf : flag active (index i)=active i := by
    unfold flag
    rw [dif_pos hb]
    rfl
  have hl : lookup table (index i)=table i := by
    unfold lookup
    rw [dif_pos hb]
    rfl
  rw [hf,hl]
  by_cases hid : i=d <;> cases ha : active i <;>
    simp [inactiveTable,without,hid,ha,he]
#print axioms selected_sum

/-- The complete extracted caller's output is the negative-sum store model. -/
theorem output_eq (table : Fin 1024 → Q) (active : Fin 1024 → Bool) (d : Fin 1024)
    (hc : ∀ i,Canonical (table i)) :
    output table active (index d)=rebalance active d table := by
  funext i
  unfold output rebalance
  rw [selected_sum table active d hc,index_val]
  have he : (i.val=d.val)↔i=d := Fin.ext_iff.symm
  rw [he]
#print axioms output_eq
end PV_L2C_SelectedDense
