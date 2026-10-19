import CuSavingsArrayFillCells

/-! Symbolic initialized-storage correspondence. No concrete array size is
normalized and no read from uninitialized storage is admitted. -/
set_option autoImplicit false
set_option maxHeartbeats 100000
namespace AspisR1.CuSavingsArrayStorage
open Aeneas Aeneas.Std Result
open CuSavingsArrayFillCells

theorem store_suffix {T : Type} (values : List T) (buffer : Slice (Option T))
    (before rest : List (Option T)) (hbuf : buffer.val = before ++ rest)
    (hlen : rest.length = values.length) :
    (store buffer before.length values).val = before ++ values.map some := by
  induction values generalizing buffer before rest with
  | nil =>
    have hr : rest = [] := List.eq_nil_of_length_eq_zero hlen
    subst rest
    simpa only [store,List.map_nil,List.append_nil] using hbuf
  | cons value values ih =>
    cases rest with
    | nil => simp only [List.length_nil,List.length_cons] at hlen; omega
    | cons old tail =>
      have ht : tail.length = values.length := by simpa only [List.length_cons] using hlen
      have hs : (buffer.setAtNat before.length (some value)).val =
          (before ++ [some value]) ++ tail := by
        simp only [Slice.setAtNat,hbuf,List.set_append_right _ _ (Nat.le_refl _),
          Nat.sub_self,List.set_cons_zero,List.append_assoc,List.singleton_append]
      have hi : (before ++ [some value]).length = before.length+1 := by simp
      have h := ih (buffer.setAtNat before.length (some value))
        (before ++ [some value]) tail hs ht
      simpa only [store,hi,List.map_cons,List.append_assoc,List.singleton_append] using h

theorem store_all {T : Type} (values : List T) (buffer : Slice (Option T))
    (hlen : buffer.length = values.length) :
    (store buffer 0 values).val = values.map some := by
  simpa only [List.length_nil,List.nil_append] using
    store_suffix values buffer [] buffer.val rfl hlen

theorem initialized_map {T : Type} (values : List T) :
    AspisR1CuArrayGraph.initializedCells (values.map some) =
      .ok ⟨values,by simp only [List.length_map]⟩ := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
    simp only [List.map_cons,AspisR1CuArrayGraph.initializedCells,ih,bind_tc_ok]

#print axioms store_suffix
#print axioms store_all
#print axioms initialized_map
end AspisR1.CuSavingsArrayStorage
