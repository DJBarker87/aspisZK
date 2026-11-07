import NMX_R3_DigestBridge
import NMX_R3_ScalarShift
set_option autoImplicit false
namespace NMX_R3_FrontierWords
open Aeneas Aeneas.Std Result NMX_R3_ByteCarrier
abbrev Row := Array U32 8#usize
abbrev Frontier := Array Row 20#usize
local instance : Inhabited Row := ⟨Array.repeat 8#usize 0#u32⟩

def row (t : Slice U8) (k : Nat) : Row := NMX_R3_DigestWords.target t (48+32*k)
def target (t : Slice U8) : Frontier := ⟨List.ofFn (fun i : Fin 20 => row t i.val), by simp⟩
def At (t : Slice U8) (next : U64) (k : Nat) : Prop :=
 NMX_R3_DigestPositive.Canonical t (48+32*k) ∧
 ((long next >>> UInt64.ofNat k) &&& 1 = 0 → row t k = NCV_ArrayFrame.coord NCV_Reference.EMPTY k)
def Valid (t : Slice U8) (next : U64) : Prop := ∀ k, k < 20 → At t next k

theorem coordinate (t : Slice U8) (k : Nat) (index : k < 20) :
 NCV_ArrayFrame.coord (target t) k = row t k := by
 simp only [NCV_ArrayFrame.coord, target,
  List.getElem?_eq_getElem (show k < (List.ofFn (fun i : Fin 20 => row t i.val)).length by simpa using index),
  List.getElem_ofFn, Option.getD_some]

/-- Same digest address at an arbitrary reached loop iteration. Extent is a
local helper input derived by the decoder's first guard at the root. -/
theorem field (t : Slice U8) (next : U64) (cap : t.val.length ≤ 768)
 (extent : 688 ≤ t.val.length) (i : Usize) (index : i.val < 20)
 (good : At t next i.val) (addr : Usize) (same : addr.val = 48+32*i.val) :
 NCV_Reference.digest t addr = ok (.Ok (NCV_ArrayFrame.coord (target t) i.val)) := by
 rw [coordinate t i.val index]
 have canonical : NMX_R3_DigestPositive.Canonical t addr.val := by
  simpa only [same] using good.1
 have call := NMX_R3_DigestPositive.value t addr cap (by omega) canonical
 simpa only [row, same] using call

theorem guard (t : Slice U8) (next : U64) (i : Usize) (index : i.val < 20)
 (good : At t next i.val) :
 ∃ tag : U64, next >>> i = ok tag ∧
  (tag &&& 1#u64 = 0#u64 →
   NCV_ArrayFrame.coord (target t) i.val = NCV_ArrayFrame.coord NCV_Reference.EMPTY i.val) := by
 refine ⟨NMX_R3_ScalarShift.tag next i, NMX_R3_ScalarShift.raw next i index, ?_⟩
 intro bit
 rw [coordinate t i.val index]
 apply good.2
 have mapped := (NMX_R3_ScalarShift.mask _).mp bit
 rwa [NMX_R3_ScalarShift.represented next i index] at mapped
#print axioms coordinate
#print axioms field
#print axioms guard
end NMX_R3_FrontierWords
