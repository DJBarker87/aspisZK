import NGV_PrefixWindow
import NGV_RowPayload
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace NGV_SemanticInitial
open AspisS1NativeCompact NGV_ByteWindow
def head (input out : Slice U8) : Result (Slice U8) := do
 let (header,back) ← core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   out {«end»:=32#usize}
 let source ← core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   input {«end»:=32#usize}
 let copied ← core.slice.Slice.copy_from_slice core.marker.CopyU8 header source
 ok (back copied)
def initial (input out : Slice U8) : Slice U8 := write out 0 (select input 0 32)
theorem compact_length : compact.COMPACT_SEMANTIC=ok 7015#usize := by
 have spec : compact.COMPACT_SEMANTIC ⦃ out => out=7015#usize ⦄ := by
   unfold compact.COMPACT_SEMANTIC compact.SEMANTIC_COMPACT_VALUES compact.LOGICAL_SEMANTIC verifier.SEMANTIC_BYTES
   step* <;> scalar_tac
 obtain ⟨out,run,value⟩:=WP.spec_imp_exists spec
 exact run.trans (congrArg ok value)
theorem logical_length : compact.LOGICAL_SEMANTIC=ok 13831#usize := by
 have spec : compact.LOGICAL_SEMANTIC ⦃ out=>out=13831#usize ⦄ := by
   unfold compact.LOGICAL_SEMANTIC verifier.SEMANTIC_BYTES
   step* <;> scalar_tac
 obtain ⟨out,run,value⟩:=WP.spec_imp_exists spec
 exact run.trans (congrArg ok value)
theorem rows : compact.SEMANTIC_ROWS=27#u8 := by
 unfold compact.SEMANTIC_ROWS
 rfl
theorem bind_assoc {α β γ : Type} (r : Result α) (f : α→Result β) (g : β→Result γ) :
 ((r >>= f) >>= g)=(r >>= fun x=>f x >>= g) := by cases r <;> rfl
theorem emitted (ops : Ops) (input out : Slice U8)
 (inputSize : input.val.length=7015) (outputSize : out.val.length=13831) :
 compact.expand_semantic ops input out=(head input out >>= fun first=>
   compact.expand_semantic_loop ops {start:=0#u8,«end»:=27#u8} input first 32#usize 32#usize) := by
 have inputLen : Slice.len input=7015#usize := UScalar.eq_of_val_eq inputSize
 have outputLen : Slice.len out=13831#usize := UScalar.eq_of_val_eq outputSize
 simp only [compact.expand_semantic,compact_length,logical_length,bind_tc_ok,inputLen,outputLen,
   bne_self_eq_false,Bool.false_eq_true,if_false,rows]
 unfold head
 simp only [bind_assoc]
 apply NGV_Monad.bind_congr (r:=core.slice.index.Slice.index_mut (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   out {«end»:=32#usize})
 rintro ⟨header,back⟩
 first | rfl | simpa only [bind_assoc,bind_tc_ok]
theorem copied (input out : Slice U8) (inputSize : input.val.length=7015) (outputSize : out.val.length=13831) :
 head input out=ok (initial input out) := by
 unfold head
 rw [NGV_PrefixWindow.read_mut out 32#usize (by scalar_tac),bind_tc_ok]
 change (core.slice.index.Slice.index (core.slice.index.SliceIndexRangeToUsizeSlice U8)
   input {«end»:=32#usize} >>= _) = _
 rw [NGV_PrefixWindow.read input 32#usize (by scalar_tac),bind_tc_ok]
 change (core.slice.Slice.copy_from_slice core.marker.CopyU8 (select out 0 32) (select input 0 32) >>= _) = _
 rw [copy (select out 0 32) (select input 0 32) (by
   rw [select_length out 0 32 (by omega),select_length input 0 32 (by omega)]),bind_tc_ok]
 rfl
#print axioms compact_length
#print axioms logical_length
#print axioms rows
#print axioms bind_assoc
#print axioms emitted
#print axioms copied
end NGV_SemanticInitial
