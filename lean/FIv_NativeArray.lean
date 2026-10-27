import FIv_Arithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIv_NativeArray
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)

def value {N : Usize} (a : Array NQ N) (n : Nat) : K :=
  match a.val[n]? with | some x => decode x | none => 0

theorem slot {N : Usize} (a : Array NQ N) (i : Usize) (z : NQ)
    (run : Array.index_usize a i=ok z) : a.val[i.val]?=some z := by
  unfold Array.index_usize at run
  split at run
  · cases run
  · rename_i x hx
    have same : x=z := Result.ok.inj run
    subst x
    exact hx

theorem read {N : Usize} (a : Array NQ N) (i : Usize) (z : NQ)
    (run : Array.index_usize a i=ok z) : value a i.val=decode z := by
  simp only [value,slot a i z run]

theorem canonical {N : Usize} (a : Array NQ N) (i : Usize) (z : NQ)
    (all : ∀ x∈a.val,Canon x) (run : Array.index_usize a i=ok z) : Canon z :=
  all z (List.mem_of_getElem? (slot a i z run))

#print axioms slot
#print axioms read
#print axioms canonical
end AspisR1.FIv_NativeArray
end
