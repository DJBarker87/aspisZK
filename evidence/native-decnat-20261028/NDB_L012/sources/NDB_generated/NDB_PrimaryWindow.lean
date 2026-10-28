import NDB_PrimaryWords
import NDB_PrimaryBytes
import NCV_CastHelpers
set_option autoImplicit false
namespace NDB_PrimaryWindow
open Aeneas Aeneas.Std Result

theorem bytes (b : Slice U8) (s : Nat) (n : Usize) (fit : s+n.val ≤ b.val.length) :
    (NDB_PrimaryWords.window b s n).val=(b.val.drop s).take n.val := by
  apply List.ext_getElem
  · simp only [NDB_PrimaryWords.window,List.length_ofFn,List.length_take,List.length_drop]
    omega
  · intro i hi hj
    have index : i<n.val := by simpa only [NDB_PrimaryWords.window,List.length_ofFn] using hi
    have inb : s+i<b.val.length := by omega
    simp [NDB_PrimaryWords.window,NCV_ZeroStep.byte,List.getElem?_eq_getElem inb]

theorem word32 (b : Slice U8) (s : Usize) (a : Array U8 4#usize)
    (fit : s.val+4 ≤ b.val.length) (field : (b.val.drop s.val).take 4=a.val) :
    NCV_Reference.word32 b s=ok (core.num.U32.from_le_bytes a) := by
  have same : NDB_PrimaryWords.window b s.val 4#usize=a := by
    apply Subtype.ext
    exact (bytes b s.val 4#usize fit).trans field
  rw [NDB_PrimaryWords.word32 b s fit,same]

theorem word64 (b : Slice U8) (s : Usize) (a : Array U8 8#usize)
    (fit : s.val+8 ≤ b.val.length) (field : (b.val.drop s.val).take 8=a.val) :
    NCV_Reference.word64 b s=ok (core.num.U64.from_le_bytes a) := by
  have same : NDB_PrimaryWords.window b s.val 8#usize=a := by
    apply Subtype.ext
    exact (bytes b s.val 8#usize fit).trans field
  rw [NDB_PrimaryWords.word64 b s fit,same]

theorem coordinate (b : Slice U8) (s : Nat) (n : Usize) (k : Nat) (index : k<n.val) :
    NCV_ArrayFrame.coord (NDB_PrimaryWords.window b s n) k=NCV_ZeroStep.byte b (s+k) := by
  simp only [NCV_ArrayFrame.coord,NDB_PrimaryWords.window,
    List.getElem?_eq_getElem (show k<(List.ofFn (fun i : Fin n.val => NCV_ZeroStep.byte b (s+i.val))).length by simpa only [List.length_ofFn] using index),
    List.getElem_ofFn,Option.getD_some]

theorem bytes32 (b : Slice U8) (s : Usize) (a : Array U8 32#usize)
    (cap : b.val.length ≤ 768) (fit : s.val+32 ≤ b.val.length)
    (field : (b.val.drop s.val).take 32=a.val) :
    NCV_Reference.bytes32 b s=ok a := by
  have same : NDB_PrimaryWords.window b s.val 32#usize=a := by
    apply Subtype.ext
    exact (bytes b s.val 32#usize fit).trans field
  apply NDB_PrimaryBytes.value b s a cap fit
  intro k hk
  rw [←same]
  exact (coordinate b s.val 32#usize k hk).symm
#print axioms bytes
#print axioms word32
#print axioms word64
#print axioms coordinate
#print axioms bytes32
end NDB_PrimaryWindow
