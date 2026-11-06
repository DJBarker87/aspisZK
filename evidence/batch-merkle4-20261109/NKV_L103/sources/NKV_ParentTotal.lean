import NKV_TreeTotal
import NKV_ParentSource
set_option autoImplicit false
noncomputable section
namespace NKV_ParentTotal
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1
open NKV_StepErasure NKV_ParentSource
open AspisV8R19.DuplexFrames
abbrev HashState := AspisV8R19.SourceDuplexStep.State

theorem read {A : Type} {size : Usize} (array : Array A size) (pos : Usize) (bound : pos.val<size.val) :
 ∃ out,Array.index_usize array pos=ok out := by
 have room : pos.val<array.val.length := by rw [array.property];exact bound
 refine ⟨array.val[pos.val]'room,?_⟩
 simp only [Array.index_usize,Array.getElem?_Usize_eq,List.getElem?_eq_getElem room]

theorem three (c0 c1 c2 : Caller)
 (total0 : ∀ i v,∃ r ai av,c0 i v=ok (r,ai,av))
 (total1 : ∀ i v,∃ r ai av,c1 i v=ok (r,ai,av))
 (total2 : ∀ i v,∃ r ai av,c2 i v=ok (r,ai,av)) :
 ∃ r,NKV_ParentSource.three c0 c1 c2=ok r := by
 rw [three_next]
 obtain ⟨r0,i0,v0,call0⟩:=total0 zeroI zeroV
 rw [call0]
 cases r0 with
 | Err e => exact ⟨.Err e,rfl⟩
 | Ok u =>
   cases u
   simp only [next,bind_tc_ok,Aeneas.Std.uncurry]
   obtain ⟨r1,i1,v1,call1⟩:=total1 i0 v0
   rw [call1]
   cases r1 with
   | Err e => exact ⟨.Err e,rfl⟩
   | Ok u =>
     cases u
     simp only [next,bind_tc_ok,Aeneas.Std.uncurry]
     obtain ⟨r2,i2,v2,call2⟩:=total2 i1 v1
     rw [call2]
     cases r2 with
     | Err e => exact ⟨.Err e,rfl⟩
     | Ok u => exact ⟨.Ok (),rfl⟩

theorem values (H : Bytes → HashState) (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (raw : Array U32 22#usize) (roots : Array (Array U8 32#usize) 3#usize) (batch : Usize)
 (hb : batch.val<2) (canonical : ∀ j,j<22 → raw.val[j]!.val<262144) :
 ∃ r,NKV_FRef.verifier.candidate.batch_merkle_values (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof raw roots batch ()=ok r := by
 obtain ⟨r0,read0⟩:=read roots 0#usize (by scalar_tac)
 obtain ⟨r1,read1⟩:=read roots 1#usize (by scalar_tac)
 obtain ⟨r2,read2⟩:=read roots 2#usize (by scalar_tac)
 obtain ⟨r,total⟩:=three
   (fun i v=>NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) proof raw r0 batch 0#usize i v ())
   (fun i v=>NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) proof raw r1 batch 1#usize i v ())
   (fun i v=>NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H) proof raw r2 batch 2#usize i v ())
   (fun i v=>NKV_TreeTotal.source H proof len p wire raw r0 batch 0#usize hb (by scalar_tac) canonical i v)
   (fun i v=>NKV_TreeTotal.source H proof len p wire raw r1 batch 1#usize hb (by scalar_tac) canonical i v)
   (fun i v=>NKV_TreeTotal.source H proof len p wire raw r2 batch 2#usize hb (by scalar_tac) canonical i v)
 refine ⟨r,?_⟩
 unfold NKV_FRef.verifier.candidate.batch_merkle_values
 rw [read0]
 simp only [bind_tc_ok]
 rw [read1]
 simp only [bind_tc_ok]
 rw [read2]
 exact total

set_option pp.proofs false
#print values
#print axioms read
#print axioms three
#print axioms values
end NKV_ParentTotal
end
