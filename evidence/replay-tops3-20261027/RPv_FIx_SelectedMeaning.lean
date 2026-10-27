import RPv_FIx_PreweightedPointwise
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_SelectedMeaning
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (K)
open FIw_ArrayValue (decoded)

def selected {N : Nat} (a : Fin N → K) (start group lane : Nat) : K :=
  if h : start≤4*group+lane ∧ 4*group+lane<start+N then
    a ⟨4*group+lane-start,by omega⟩ else 0

def contribution {N : Nat} (a : Fin N → K) (start group : Nat) : K :=
  FIx_PreweightedPack.pack (fun i=>selected a start group i.val)

theorem read {N : Usize} (a : Array NQ N) (i : Nat) (hi : i<N.val) :
    FIv_NativeArray.value a i=decoded a ⟨i,hi⟩ := by
  unfold FIv_NativeArray.value decoded FIw_ArrayValue.cells
  rw [List.getElem?_eq_getElem (by simpa only [a.property] using hi)]

theorem value {N : Usize} (a : Array NQ N) (model : Fin N.val → K) (same : decoded a=model)
    (start group lane : Nat) :
    FIx_PreweightedSelect.selected a start group lane=selected model start group lane := by
  unfold FIx_PreweightedSelect.selected selected
  split
  · rename_i h
    rw [read a _ (by omega),same]
  · rfl

theorem increment {N : Usize} (a : Array NQ N) (model : Fin N.val → K) (same : decoded a=model)
    (start group : Nat) :
    FIx_PreweightedGroup.increment a start group=contribution model start group := by
  unfold FIx_PreweightedGroup.increment contribution
  congr 1
  funext i
  exact value a model same start group i.val
#print axioms read
#print axioms value
#print axioms increment
end AspisR1.FIx_SelectedMeaning
end
