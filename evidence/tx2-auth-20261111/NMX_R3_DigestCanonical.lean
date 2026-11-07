import NMX_R3_DigestPositive
import NMX_R3_DigestCarrier
import NMX_R3_ByteIndex
set_option autoImplicit false
namespace NMX_R3_DigestCanonical
open Aeneas Aeneas.Std RSL NMX_R3_ByteCarrier NMX_R3_DigestWords NMX_R3_DigestCarrier
attribute [local instance] Classical.propDecidable

theorem point (b : Slice U8) (s k : Nat) (index : k < 8) :
 RSL.le32 ((slice (b.val.map byte) s (s+32)).getD (4*k) 0)
  ((slice (b.val.map byte) s (s+32)).getD (4*k+1) 0)
  ((slice (b.val.map byte) s (s+32)).getD (4*k+2) 0)
  ((slice (b.val.map byte) s (s+32)).getD (4*k+3) 0) =
 NMX_R3_WordRead.valueAt b (s+4*k) := by
 rw [NMX_R3_ByteIndex.window b s 32 (4*k) (by omega),
  NMX_R3_ByteIndex.window b s 32 (4*k+1) (by omega),
  NMX_R3_ByteIndex.window b s 32 (4*k+2) (by omega),
  NMX_R3_ByteIndex.window b s 32 (4*k+3) (by omega)]
 simp only [NMX_R3_WordRead.valueAt, Nat.add_assoc]

theorem limbs (b : Slice U8) (s : Nat) :
 (List.range 8).map (fun k =>
  RSL.le32 ((slice (b.val.map byte) s (s+32)).getD (4*k) 0)
   ((slice (b.val.map byte) s (s+32)).getD (4*k+1) 0)
   ((slice (b.val.map byte) s (s+32)).getD (4*k+2) 0)
   ((slice (b.val.map byte) s (s+32)).getD (4*k+3) 0)) = words b s := by
 apply List.ext_getElem
 · simp only [words, List.length_map]
 · intro k hk hj
   simp only [words, List.getElem_map, List.getElem_range]
   exact point b s k (by simpa only [List.length_map, List.length_range] using hk)

theorem canonical (b : Slice U8) (s : Nat) :
 NMX_R3_DigestPositive.Canonical b s ↔
 (words b s).all (fun w => decide (w < P31)) = true := by
 rw [← words_exact b s]
 simp only [List.all_map, Function.comp_def, List.all_eq_true,
  decide_eq_true_eq, canonical_limb]
 constructor
 · intro h x hx
   obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
   simpa only [target, List.getElem_ofFn] using
    h k (by simpa only [target, List.length_ofFn] using hk)
 · intro h k hk
   have bound : k < (target b s).val.length := by
    simpa only [target, List.length_ofFn] using hk
   have good := h (target b s).val[k] (List.getElem_mem bound)
   simpa only [target, List.getElem_ofFn] using good

/-- Exact canonical digest decision for the same original 32-byte window.
Default-zero behavior is preserved even before the caller proves extent. -/
theorem value (b : Slice U8) (s : Nat) :
 TX2_217.decodeDigestCanonical (slice (b.val.map byte) s (s+32)) =
 if NMX_R3_DigestPositive.Canonical b s then some (words b s) else none := by
 classical
 unfold TX2_217.decodeDigestCanonical
 rw [limbs b s]
 by_cases h : NMX_R3_DigestPositive.Canonical b s
 · simp only [h, if_pos, (canonical b s).mp h]
 · have no : (words b s).all (fun w => decide (w < P31)) = false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    exact h ((canonical b s).mpr yes)
   simp only [h, if_neg, no, Bool.false_eq_true, ↓reduceIte]
#print axioms point
#print axioms limbs
#print axioms canonical
#print axioms value
end NMX_R3_DigestCanonical
