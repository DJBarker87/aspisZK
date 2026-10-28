import NDE_ArrayExt
import NDE_PackedTotal
import NDN_PackedReference
set_option autoImplicit false
namespace NDN_KMXCopyMeaning
/-- Value-level semantics for explicit indexed writes. Pointer validity,
non-overlap, lengths and allocation remain caller obligations. -/
def write {α : Type} (dst : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun k => if k = i then v else dst k

def loop {α : Type} (src dst : Nat → α) (start : Nat) : Nat → Nat → α
  | 0 => dst
  | n+1 => loop src (write dst start (src start)) (start+1) n

theorem loop_spec {α : Type} (src dst : Nat → α) (start count k : Nat) :
    loop src dst start count k =
      if start ≤ k ∧ k < start + count then src k else dst k := by
  induction count generalizing dst start with
  | zero =>
    have h : ¬ (start ≤ k ∧ k < start + 0) := by omega
    simp only [loop, if_neg h]
  | succ n ih =>
    rw [loop, ih]
    by_cases hk : k = start
    · subst k
      have hn : ¬ (start + 1 ≤ start ∧ start < start + 1 + n) := by omega
      have hy : start ≤ start ∧ start < start + (n + 1) := by omega
      simp only [if_neg hn, if_pos hy, write, if_pos rfl]
    · by_cases h : start + 1 ≤ k ∧ k < start + 1 + n
      · have hy : start ≤ k ∧ k < start + (n + 1) := by omega
        simp only [if_pos h, if_pos hy]
      · have hn : ¬ (start ≤ k ∧ k < start + (n + 1)) := by omega
        simp only [if_neg h, if_neg hn, write, if_neg hk]

theorem copy_prefix {α : Type} (src dst : Nat → α) (count k : Nat) :
    loop src dst 0 count k = if k < count then src k else dst k := by
  simpa using loop_spec src dst 0 count k

theorem copy_frame {α : Type} (src dst : Nat → α) (start count k : Nat)
    (outside : k < start ∨ start + count ≤ k) :
    loop src dst start count k = dst k := by
  rw [loop_spec, if_neg]; omega

/-- Vector append value law. This says nothing about allocation failure,
capacity, pointer identity, or the allocator's reallocation implementation. -/
def appendLoop {α : Type} (dst : List α) : List α → List α
  | [] => dst
  | x::xs => appendLoop (dst ++ [x]) xs

theorem append_spec {α : Type} (dst src : List α) :
    appendLoop dst src = dst ++ src := by
  induction src generalizing dst with
  | nil => simp [appendLoop]
  | cons x xs ih => simp [appendLoop, ih, List.append_assoc]

/-- Successful reallocation preserves the overlapping byte prefix. Allocation
success, ownership and uninitialized-byte validity are external obligations. -/
theorem realloc_prefix {α : Type} (src dst : Nat → α) (oldSize newSize k : Nat) :
    loop src dst 0 (min oldSize newSize) k =
      if k < min oldSize newSize then src k else dst k :=
  copy_prefix src dst (min oldSize newSize) k

#print axioms realloc_prefix
#print axioms loop_spec
#print axioms copy_prefix
#print axioms copy_frame
#print axioms append_spec
end NDN_KMXCopyMeaning

set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace NDN_PackedFrame
open AspisR1
open FJb_TailCell (cell)

theorem vector {α : Type} (a b : Array α 4#usize)
    (h : ∀ i : Fin 4, cell a i = cell b i) : a=b := by
  apply NDE_ArrayExt.bounded_words
  intro i hi
  have ha : i<a.val.length := by rw [a.property];exact hi
  have hb : i<b.val.length := by rw [b.property];exact hi
  rw [List.getElem?_eq_getElem ha,List.getElem?_eq_getElem hb]
  exact congrArg some (h ⟨i,hi⟩)

theorem table {α : Type} (a b : Array (Array α 4#usize) 4#usize)
    (h : ∀ r j : Fin 4, cell (cell a r) j = cell (cell b r) j) : a=b := by
  apply vector
  intro r
  exact vector _ _ (h r)

theorem copied_window {α : Type} (src dst : Nat → α) (start count i : Nat)
    (inside : start ≤ i ∧ i<start+count) :
    NDN_KMXCopyMeaning.loop src dst start count i=src i := by
  rw [NDN_KMXCopyMeaning.loop_spec,if_pos inside]

theorem result (input : Array FIv_NativeArithmetic.NQ 4#usize)
    (hc : FIw_ArrayValue.canonical input) :
    ∃ out, FIq_Native.state_only_poseidon.external_local_packed_raw input=ok out ∧
      ∀ j : Fin 4, (cell out j).val = PoseidonExternalPackedAlgebra.packedNat
        (7*AspisV8R15.ExactTowerBase.P) (FJe_PackedRawValue.matrix input) j := by
  obtain ⟨out,run⟩ := NDE_PackedTotal.source input hc
  exact ⟨out,run,FJe_PackedRawValue.value input out hc run⟩

#print axioms vector
#print axioms table
#print axioms copied_window
#print axioms result
end NDN_PackedFrame
end

