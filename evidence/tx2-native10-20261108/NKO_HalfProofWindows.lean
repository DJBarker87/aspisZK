import NKO_ProofWindows
set_option autoImplicit false
noncomputable section
namespace NKO_HalfProofWindows
open Aeneas Aeneas.Std Result
def Window (before after : Slice U8) (block : Fin 14) : Prop :=
 ∀ i,i<4096 → after.val[4096*block.val+i]?=before.val[4096*block.val+i]?
def Tail (before after : Slice U8) : Prop :=
 ∀ i,i<263 → after.val[57344+i]?=before.val[57344+i]?

theorem retained_tail (before after : Slice U8)
 (window : NKO_ProofWindows.Window before after ⟨7,by omega⟩) : Tail before after := by
 intro i inside
 exact window i (by omega) (by omega)

theorem cover (before after : Slice U8) (windows : ∀ block,Window before after block)
 (tail : Tail before after) (i : Nat) (inside : i<57607) : after.val[i]?=before.val[i]? := by
 by_cases inPrefix : i<57344
 · have blockBound : i/4096<14 := by omega
   have laneBound : i%4096<4096 := Nat.mod_lt _ (by omega)
   have index : 4096*(i/4096)+i%4096=i := by omega
   have same := windows ⟨i/4096,blockBound⟩ (i%4096) laneBound
   simpa only [index] using same
 · have offset : 57344+(i-57344)=i := by omega
   have same := tail (i-57344) (by omega)
   simpa only [offset] using same

theorem same (before after : Slice U8) (oldSize : before.val.length=57607)
 (newSize : after.val.length=57607) (windows : ∀ block,Window before after block)
 (tail : Tail before after) : after=before := by
 apply Subtype.ext
 apply List.ext_getElem?
 intro i
 by_cases inside : i<57607
 · exact cover before after windows tail i inside
 · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]
#print axioms retained_tail
#print axioms cover
#print axioms same
end NKO_HalfProofWindows
