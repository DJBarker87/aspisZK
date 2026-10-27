import RPt_FJc_WeightConstants
import RPt_FJc_ArrayRead
import RPt_FIo_ArrayCanon
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJc_WeightArray
open Aeneas Aeneas.Std Result
open FJc_WeightQMBridge (SQ)
open FJc_WeightValues (Canon decode)
def canonical {N : Usize} (a : Array SQ N) : Prop := ∀ x∈a.val,Canon x
def value {N : Usize} (a : Array SQ N) (i : Nat) : OraclePortCheckpointAbiC5.K :=
  match a.val[i]? with | some x => decode x | none => 0

theorem slot {N : Usize} (a : Array SQ N) (i : Usize) (x : SQ)
    (run : Array.index_usize a i=ok x) : a.val[i.val]?=some x := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i v hv
    cases Result.ok.inj run
    exact hv

theorem read {N : Usize} (a : Array SQ N) (i : Usize) (x : SQ)
    (run : Array.index_usize a i=ok x) : value a i.val=decode x := by
  simp only [value,slot a i x run]

theorem canonical_read {N : Usize} (a : Array SQ N) (i : Usize) (x : SQ)
    (ha : canonical a) (run : Array.index_usize a i=ok x) : Canon x :=
  ha x (List.mem_of_getElem? (slot a i x run))

theorem update {N : Usize} (a b : Array SQ N) (i : Usize) (x : SQ)
    (ha : canonical a) (hx : Canon x) (run : Array.update a i x=ok b) : canonical b := by
  unfold Array.update at run
  split at run
  · cases run
  · cases Result.ok.inj run
    exact FIo_ArrayCanon.list_set Canon _ _ x ha hx

#print axioms slot
#print axioms read
#print axioms canonical_read
#print axioms update
end AspisR1.FJc_WeightArray
end
