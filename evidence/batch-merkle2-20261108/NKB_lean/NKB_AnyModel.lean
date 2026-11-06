import NKB_PaddingPredicate
import Port4B_AnyFalse

set_option autoImplicit false
noncomputable section
namespace NKB_AnyModel
open Aeneas Aeneas.Std Result ControlFlow AspisR1

/-- Concrete callback; no arbitrary Ops or free runtime Bool. -/
abbrev predicate :=
 NJS_Extract.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool
   (NJS_RuntimeDigest.backend (fun _ => default))

def nonzero (chunk : Slice U8) : Bool :=
 if size : chunk.val.length=8 then
   core.num.U64.from_le_bytes (⟨chunk.val,size⟩ : Array U8 8#usize) != 0#u64
 else true

def scan : List (Slice U8) → Bool × List (Slice U8)
 | [] => (false,[])
 | chunk::rest => if nonzero chunk then (true,rest) else scan rest

theorem callback (chunk : Slice U8) (size : chunk.val.length=8) :
 predicate.call_mut () chunk=ok (nonzero chunk,()) := by
 change NKB_PaddingPredicate.callback chunk=ok (nonzero chunk,())
 rw [NKB_PaddingPredicate.source chunk size]
 simp only [nonzero,dif_pos size]

/-- Complete finite Iterator::any law over the pinned ChunksExact model,
including true short-circuit, false exhaustion, remaining chunks and remainder.
Native constructor/next fidelity: K017/K018; predicate fidelity: K015/K016.
The body equations used below are rfl on the pinned Aeneas std definition. -/
theorem total (chunks : List (Slice U8)) (remainder : Slice U8)
    (full : ∀ c∈chunks,c.val.length=8) :
 Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorChunksExact U8) predicate
   {chunks:=chunks,remainder:=remainder} () =
   ok ((scan chunks).1,{chunks:=(scan chunks).2,remainder:=remainder}) := by
 induction chunks with
 | nil =>
   unfold Port3_BatchStd.anyDefault
   rw [Aeneas.Std.loop.eq_def,Port4B_AnyFalse.body_nil]
   rfl
 | cons chunk rest ih =>
   have call := callback chunk (full chunk (by simp))
   have tail := ih (fun c hc => full c (by simp only [List.mem_cons];exact Or.inr hc))
   cases h : nonzero chunk with
   | true =>
     have body : Port3_BatchStd.anyBody (core.iter.traits.iterator.IteratorChunksExact U8) predicate
         ({chunks:=chunk::rest,remainder:=remainder},()) =
         ok (.done (true,{chunks:=rest,remainder:=remainder})) := by
       rw [Port4B_AnyFalse.body_cons,call]
       simp [h]
     unfold Port3_BatchStd.anyDefault
     rw [Aeneas.Std.loop.eq_def,body]
     simp only [scan,h,if_true]
   | false =>
     have body : Port3_BatchStd.anyBody (core.iter.traits.iterator.IteratorChunksExact U8) predicate
         ({chunks:=chunk::rest,remainder:=remainder},()) =
         ok (.cont ({chunks:=rest,remainder:=remainder},())) := by
       rw [Port4B_AnyFalse.body_cons,call]
       simp [h]
     unfold Port3_BatchStd.anyDefault
     rw [Aeneas.Std.loop.eq_def,body]
     change Port3_BatchStd.anyDefault (core.iter.traits.iterator.IteratorChunksExact U8) predicate
       {chunks:=rest,remainder:=remainder} () = _
     simpa only [scan,h,Bool.false_eq_true,if_false] using tail

theorem predicate_false (chunk : Slice U8) (size : chunk.val.length=8) :
 nonzero chunk=false ↔ ∀ b∈chunk.val,b=0#u8 := by
 simpa [nonzero,size] using NKB_PaddingPredicate.zero_iff (⟨chunk.val,size⟩ : Array U8 8#usize)

/-- Both outcomes of the hand library model are tied to exact bytes, rather
than postulating zero padding from a successful whole batch. -/
theorem false_iff (chunks : List (Slice U8)) (full : ∀ c∈chunks,c.val.length=8) :
 (scan chunks).1=false ↔ ∀ c∈chunks,∀ b∈c.val,b=0#u8 := by
 induction chunks with
 | nil => simp only [scan,List.not_mem_nil,IsEmpty.forall_iff,implies_true]
 | cons chunk rest ih =>
   have tail := ih (fun c hc => full c (by simp only [List.mem_cons];exact Or.inr hc))
   by_cases zeros : ∀ b∈chunk.val,b=0#u8
   · have h := (predicate_false chunk (full chunk (by simp))).mpr zeros
     simp only [scan,h,Bool.false_eq_true,if_false]
     constructor
     · intro result c member
       rcases List.mem_cons.mp member with eq|mem
       · subst c;exact zeros
       · exact tail.mp result c mem
     · intro all
       exact tail.mpr (fun c hc => all c (List.mem_cons_of_mem _ hc))
   · have h : nonzero chunk=true := by
       cases eq : nonzero chunk with
       | true => rfl
       | false => exact (zeros ((predicate_false chunk (full chunk (by simp))).mp eq)).elim
     simp only [scan,h,if_true]
     constructor
     · intro impossible;cases impossible
     · intro all;exact (zeros (all chunk (by simp))).elim

#print axioms callback
#print axioms total
#print axioms predicate_false
#print axioms false_iff
end NKB_AnyModel
end
