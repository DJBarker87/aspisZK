import NMP_PrepareSource
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_PrepareExpansionError
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted NMP_PrepareSteps
open NMT_CallTree (run Event)
/-- Even a mutable expansion Err retains only its reached call and old g. -/
theorem stopped_prefix {H W : Type} (c : Calls) (s : Parent H W) (semantic y1 src after : Slice U8)
 (back : SplitBack) (vecBack : VecBack) (e : compact.CodecError)
 (index : core.slice.index.Slice.index (core.slice.index.SliceIndexRangeUsizeSlice U8)
    s.bytes {start:=16#usize,«end»:=7031#usize} = .ok src)
 (h : c.c10 src semantic = .ok (.Err e,after)) :
 run (execute c 6 (.semantic s semantic y1 back vecBack)) =
 (.ok (.Err verifier.Error.Parse,s.scratch),[Event.call "TX1:098/expand_semantic" (src,semantic)
  (.ok ((.Err e : core.result.Result Unit compact.CodecError),after))]) := by
 rw [execute]
 simp only [step]
 rw [index]
 change run (do
   let pair ← NMT_CallTree.invoke "TX1:098/expand_semantic" (src,semantic) (c.c10 src semantic)
   let r ← (match pair.1 with
      | .Err _ => pure (.inl (.Err verifier.Error.Parse,s.scratch))
      | .Ok _ => pure (.inr (.values s pair.2 y1 back vecBack)))
   match r with
   | .inl out => pure out
   | .inr next => execute c 5 next) = _
 rw [h]
 rfl
#print axioms stopped_prefix
end AspisR1.NMP_PrepareExpansionError
