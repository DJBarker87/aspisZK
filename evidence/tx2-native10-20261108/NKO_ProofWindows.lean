import NKE_ViewWindows
set_option autoImplicit false
noncomputable section
namespace NKO_ProofWindows
open Aeneas Aeneas.Std Result
/-- Every native proof window has the complete actual57607-byte carrier.
Only the observation index is partitioned; no unobserved byte is zeroed. -/
def Window (before after : Slice U8) (block : Fin 8) : Prop :=
 ∀ i,i<8192 → 8192*block.val+i<57607 →
 after.val[8192*block.val+i]?=before.val[8192*block.val+i]?

theorem cover (before after : Slice U8) (windows : ∀ block,Window before after block)
 (i : Nat) (inside : i<57607) : after.val[i]?=before.val[i]? := by
 have blockBound : i/8192<8 := by omega
 have laneBound : i%8192<8192 := Nat.mod_lt _ (by omega)
 have index : 8192*(i/8192)+i%8192=i := by omega
 have same := windows ⟨i/8192,blockBound⟩ (i%8192) laneBound (by simpa only [index] using inside)
 simpa only [index] using same

theorem same (before after : Slice U8) (oldSize : before.val.length=57607)
 (newSize : after.val.length=57607) (windows : ∀ block,Window before after block) : after=before := by
 apply Subtype.ext
 apply List.ext_getElem?
 intro i
 by_cases inside : i<57607
 · exact cover before after windows i inside
 · rw [List.getElem?_eq_none (by omega),List.getElem?_eq_none (by omega)]

/-- The disjoint observations cover the entire carrier exactly once. -/
theorem disjoint (b c : Fin 8) (i j : Nat) (ib : i<8192) (jb : j<8192)
 (same : 8192*b.val+i=8192*c.val+j) : b=c ∧ i=j := by
 have bc : b.val=c.val := by omega
 exact ⟨Fin.ext bc,by omega⟩
#print axioms cover
#print axioms same
#print axioms disjoint
end NKO_ProofWindows
