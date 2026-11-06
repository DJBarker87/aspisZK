import NKV_ConcreteChildren
import NKB_AnyModel
set_option autoImplicit false
noncomputable section
namespace NKV_PaddingInstall
open Aeneas Aeneas.Std Result AspisR1
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

/-- Iterator::any observes call_mut only; no assumed whole-scan result. -/
theorem any_congr {Self F Item : Type} (iter : core.iter.traits.iterator.Iterator Self Item)
 (a b : core.ops.function.FnMut F Item Bool) (same : a.call_mut=b.call_mut) (s : Self) (f : F) :
 Port3_BatchStd.anyDefault iter a s f=Port3_BatchStd.anyDefault iter b s f := by
 have body : Port3_BatchStd.anyBody iter a=Port3_BatchStd.anyBody iter b := by
   funext state
   unfold Port3_BatchStd.anyBody
   rw [same]
 unfold Port3_BatchStd.anyDefault
 rw [body]

abbrev predicate (H : Bytes → HashState) :=
 Port3_NativeBatchBody.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
   (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)

theorem callback (H : Bytes → HashState) : (predicate H).call_mut=NKB_AnyModel.predicate.call_mut := by
 funext state chunk
 cases state
 rfl

/-- The installed SOURCE callback and arbitrary full chunks, including the
true short-circuit and remaining iterator, reuse the CLOSED native any law. -/
theorem total (H : Bytes → HashState) (chunks : List (Slice U8)) (remainder : Slice U8)
 (full : ∀ c∈chunks,c.val.length=8) :
 (NKV_ConcreteChildren.ops H).op0 (core.iter.traits.iterator.IteratorChunksExact U8)
   (predicate H) {chunks:=chunks,remainder:=remainder} ()=
 ok ((NKB_AnyModel.scan chunks).1,{chunks:=(NKB_AnyModel.scan chunks).2,remainder:=remainder}) := by
 change Port3_BatchStd.anyDefault _ _ _ _=_
 rw [any_congr _ _ NKB_AnyModel.predicate (callback H)]
 exact NKB_AnyModel.total chunks remainder full

#print any_congr
#print callback
#print total
#print axioms any_congr
#print axioms callback
#print axioms total
end NKV_PaddingInstall
end
