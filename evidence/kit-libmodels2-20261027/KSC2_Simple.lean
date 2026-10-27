import KSC2_P7
open Aeneas Aeneas.Std Result
namespace KSC2
-- Rust 1.94.1 Option::ok_or: both value arms, no library panic.
theorem option_ok_or {T E : Type} (s : Option T) (e : E) :
    KSA_Isolated.core.option.Option.ok_or s e =
      ok (match s with | some t => core.result.Result.Ok t | none => .Err e) := by
  cases s <;> rfl
-- Rust 1.94.1 Result::unwrap_or_else: a callback is executed exactly on Err.
-- Its entire Result is preserved, including failure and divergence.
theorem unwrap_or_else {T E F : Type} (f : core.ops.function.FnOnce F E T)
    (s : core.result.Result T E) (c : F) :
    KSA_Isolated.core.result.Result.unwrap_or_else f s c =
      match s with | .Ok t => ok t | .Err e => f.call_once c e := by
  cases s <;> rfl
-- Rust Iterator::map is a lazy constructor: it stores, and does not call, f.
theorem map_lazy {I T U F : Type} (it : core.iter.traits.iterator.Iterator I T)
    (f : core.ops.function.FnMut F T U) (s : I) (c : F) :
    KSA_Isolated.core.iter.traits.iterator.Iterator.map.default it f s c =
      ok (⟨s,c⟩ : core.iter.adapters.map.Map I F) := rfl
-- Valid Windows states have positive width; constructor enforces this.
theorem windows_zero {T : Type} (s : Slice T) :
    KSA_Isolated.core.slice.Slice.windows s 0#usize = fail .panic := by rfl
theorem windows_positive {T : Type} (s : Slice T) (w : Usize) (hw : w ≠ 0#usize) :
    KSA_Isolated.core.slice.Slice.windows s w =
      ok (⟨s,w,0⟩ : KSA_Isolated.core.slice.iter.Windows T) := by
  simp only [KSA_Isolated.core.slice.Slice.windows, hw, ↓reduceIte]
theorem window_contents {T : Type} (s : Slice T) (i w : Nat) :
    (KSA_Isolated.core.slice.iter.Windows.windowAt s i w).val =
      (s.val.drop i).take w := rfl
theorem windows_next_some {T : Type} (s : KSA_Isolated.core.slice.iter.Windows T)
    (h : s.index + s.width.val ≤ s.slice.val.length) :
    KSA_Isolated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next s =
      ok (some (KSA_Isolated.core.slice.iter.Windows.windowAt s.slice s.index s.width.val),
        {s with index := s.index + 1}) := by
  simp only [KSA_Isolated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,
    h, ↓reduceIte]
theorem windows_next_none {T : Type} (s : KSA_Isolated.core.slice.iter.Windows T)
    (h : ¬ s.index + s.width.val ≤ s.slice.val.length) :
    KSA_Isolated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next s =
      ok (none,s) := by
  simp only [KSA_Isolated.core.slice.iter.Windows.Insts.CoreIterTraitsIteratorIteratorSharedASlice.next,
    h, ↓reduceIte]
theorem shared_back_some {T : Type} (s : core.slice.iter.Iter T)
    (h : s.i < s.slice.val.length) :
    KSA_Isolated.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back s =
      ok (s.slice.val.getLast?, {s with slice := ⟨s.slice.val.dropLast, by
        rw [List.length_dropLast]
        exact Nat.le_trans (Nat.sub_le _ _) s.slice.property⟩}) := by
  simp only [KSA_Isolated.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    h, ↓reduceIte]
theorem shared_back_none {T : Type} (s : core.slice.iter.Iter T)
    (h : ¬ s.i < s.slice.val.length) :
    KSA_Isolated.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back s =
      ok (none,s) := by
  simp only [KSA_Isolated.core.slice.iter.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
    h, ↓reduceIte]
#print axioms option_ok_or
#print axioms unwrap_or_else
#print axioms map_lazy
#print axioms windows_zero
#print axioms windows_positive
#print axioms window_contents
#print axioms windows_next_some
#print axioms windows_next_none
#print axioms shared_back_some
#print axioms shared_back_none
end KSC2
