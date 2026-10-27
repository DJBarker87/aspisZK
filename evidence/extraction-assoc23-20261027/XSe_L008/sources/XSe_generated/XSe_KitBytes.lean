import XSe_OldBytes
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XSe_KitBytes
open XSe_ByteWindows
/-- Kernel-small list shape: the eight windows are exactly the read limbs. -/
theorem words (s : Slice U8) (size : s.val.length=32) :
 (List.range 8).map (fun i => XRn_Join_word ((s.val.drop (4*i)).take 4))=
 (XSe_OldBytes.words s).val := by
 simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil]
 simp only [List.nil_append,List.cons_append]
 simp only [Nat.reduceMul]
 simp only [window s 0 (by omega),
  window s 4 (by omega),
  window s 8 (by omega),
  window s 12 (by omega),
  window s 16 (by omega),
  window s 20 (by omega),
  window s 24 (by omega),
  window s 28 (by omega),XSe_OldBytes.words,Array.make]
/-- Total byte decoder equals its limb decoder on the exact32-byte domain. -/
theorem source (s : Slice U8) (size : s.val.length=32) :
 _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes s=
 _root_.aspis_core.field.wide_exact.WideExact.from_limbs (XSe_OldBytes.words s) := by
 unfold _root_.aspis_core.field.wide_exact.WideExact.from_le_bytes
 rw [words s size]
 simp only [size,true_and]
 rfl
#print axioms words
#print axioms source
end XSe_KitBytes
