import NMX_R3_FrontierWords
import NMX_R3_DigestEquality
import NMX_R3_Constants
import NMX_R3_ListRead
set_option autoImplicit false
namespace NMX_R3_FrontierCarrier
open Aeneas Aeneas.Std RSL NMX_R3_ByteCarrier NMX_R3_FrontierWords
attribute [local instance] Classical.propDecidable
local instance : Inhabited Row := ⟨Array.repeat 8#usize 0#u32⟩

def hostRow (t : Slice U8) (k : Nat) : Digest := (row t k).val.map word
def rows (t : Slice U8) (n : Nat) : List Digest := (List.range n).map (hostRow t)

theorem empty_coordinate (k : Nat) (index : k < 21) :
 (NCV_ArrayFrame.coord NCV_Reference.EMPTY k).val.map word = EMPTY_ROOTS.getD k [] := by
 have bound : k < NCV_Reference.EMPTY.val.length := by
  have length : NCV_Reference.EMPTY.val.length = 21 := NCV_Reference.EMPTY.property
  omega
 rw [← NMX_R3_Constants.empty,
  NMX_R3_ListRead.getD _ k (by simpa only [List.length_map] using bound) []]
 simp only [NCV_ArrayFrame.coord, List.getElem?_eq_getElem bound,
  Option.getD_some, List.getElem_map]

theorem equal (t : Slice U8) (k : Nat) (index : k < 20) :
 hostRow t k = EMPTY_ROOTS.getD k [] ↔
 row t k = NCV_ArrayFrame.coord NCV_Reference.EMPTY k := by
 rw [← empty_coordinate k (by omega)]
 exact ⟨fun h => NMX_R3_DigestEquality.rows_injective h,
  fun h => congrArg (fun a : Row => a.val.map word) h⟩

theorem digest (t : Slice U8) (k : Nat) :
 TX2_217.decodeDigestCanonical (slice (t.val.map byte) (48+32*k) (48+32*k+32)) =
 if NMX_R3_DigestPositive.Canonical t (48+32*k) then some (hostRow t k) else none := by
 simpa only [hostRow, row, NMX_R3_DigestCarrier.words_exact] using
  NMX_R3_DigestCanonical.value t (48+32*k)

theorem good_guard (t : Slice U8) (next : U64) (k : Nat) (index : k < 20)
 (good : At t next k) :
 ((long next >>> UInt64.ofNat k) &&& 1 == 0 && hostRow t k != EMPTY_ROOTS.getD k []) = false := by
 apply Bool.eq_false_iff.mpr
 intro bad
 simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at bad
 exact bad.2 ((equal t k index).mpr (good.2 bad.1))

theorem bad_guard (t : Slice U8) (next : U64) (k : Nat) (index : k < 20)
 (canonical : NMX_R3_DigestPositive.Canonical t (48+32*k)) (rejected : ¬ At t next k) :
 ((long next >>> UInt64.ofNat k) &&& 1 == 0 && hostRow t k != EMPTY_ROOTS.getD k []) = true := by
 simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne]
 constructor
 · by_contra occupied
   exact rejected ⟨canonical, fun h => False.elim (occupied h)⟩
 · intro same
   exact rejected ⟨canonical, fun _ => (equal t k index).mp same⟩

theorem rows_exact (t : Slice U8) : (target t).val.map (fun a => a.val.map word) = rows t 20 := by
 apply List.ext_getElem
 · simp only [target, rows, List.length_map, List.length_ofFn, List.length_range]
 · intro k hk hj
   simp only [target, rows, List.getElem_map, List.getElem_ofFn, List.getElem_range, hostRow]
#print axioms empty_coordinate
#print axioms equal
#print axioms digest
#print axioms good_guard
#print axioms bad_guard
#print axioms rows_exact
end NMX_R3_FrontierCarrier
