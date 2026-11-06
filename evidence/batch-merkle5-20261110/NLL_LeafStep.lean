import NLL_Invocation
set_option autoImplicit false
noncomputable section
namespace NLL_LeafStep
open Aeneas Aeneas.Std Result ControlFlow AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep AspisV8R19.SqueezeOracleBridge

/-- SAME decoded key, physical opening and runtime byte slices. The native
cut digest is the existing runtime H interpretation; no hash body is unfolded. -/
theorem source (H : Bytes → AspisV8R19.SourceDuplexStep.State)
 (proof : Slice U8) (len : proof.val.length=57607)
 (p : OraclePortCompactDraft.Parsed) (wire : p.wire=MultiproofConeCanonical.bytesOf proof.val)
 (q : Fin 22 → Fin 262144) (batch selected : Nat) (kind lo n slot : Usize)
 (root : NLL.Root) (f : Frame)
 (mem : selected∈OraclePortFrozenOrder.sortedPositions q batch kind.val)
 (loValue : lo.val=(if batch=0 then 0 else 10)) (more : f.position<n) (room : f.scratch.n.val<16)
 (keyRead : Array.index_usize f.keys f.position=ok (MultiproofConeSortOrder.packed q batch kind.val selected)) :
 Port4B_NativeLeaf.decodedIndex (key f)=MultiproofConeLeafFold.key q kind.val selected ∧
 flatten (Port4B_LeafCode.input kind (view H proof lo (key f)))=OraclePortSelectedDraft.leaf p kind.val selected ∧
 digest H proof kind lo f=encodeState (H (OraclePortSelectedDraft.leaf p kind.val selected)) ∧
 NKV_FRef.verifier.candidate.batch_tree_loop.body (NKV_ConcreteChildren.ops H)
   (NKV_ConcreteChildren.digest H) proof root kind () lo n slot f.keys
     f.scratch.idx f.scratch.val f.scratch.n f.position=
 (do let out ← reference.leaf_step f.scratch (Port4B_NativeLeaf.decodedIndex (key f))
       (digest H proof kind lo f)
     ok (NKV_LeafStep.project f.scratch (Usize.wrapping_add f.position 1#usize) out)) := by
 have packed : key f=MultiproofConeSortOrder.packed q batch kind.val selected := by
   unfold key
   simp only [Array.index_usize,Array.getElem?_Usize_eq] at keyRead
   cases h : f.keys.val[f.position.val]? with
   | none => rw [h] at keyRead;cases keyRead
   | some k =>
     rw [h] at keyRead
     have same:=Result.ok.inj keyRead
     simpa only [List.getElem!_eq_getElem?_getD,h,Option.getD_some] using same
 obtain ⟨physical,read,width,address,reads,body⟩:=NKV_LeafInvocation.source H proof len p wire q batch selected
   kind lo n slot f.position root f.keys f.scratch mem loValue more room keyRead []
 have selectedView : view H proof lo (key f)=physical := by
   unfold view
   rw [packed,read]
 have member:=MultiproofConeKeyAdapters.sorted_member q batch kind.val selected mem
 have decoded:=Port4B_KeyDecode.packed q batch kind.val selected member lo loValue
 have indexEq : Port4B_NativeLeaf.decodedIndex (key f)=MultiproofConeLeafFold.key q kind.val selected := by
   rw [packed]
   exact UScalar.eq_of_val_eq decoded.1
 have addr : flatten (Port4B_LeafCode.input kind (view H proof lo (key f)))=OraclePortSelectedDraft.leaf p kind.val selected := by
   rw [selectedView];exact address
 have hashEq : digest H proof kind lo f=encodeState (H (OraclePortSelectedDraft.leaf p kind.val selected)) := by
   unfold digest
   rw [addr]
 exact ⟨indexEq,addr,hashEq,by rw [indexEq,hashEq];exact body⟩

set_option pp.proofs false
#print source
#print axioms source
end NLL_LeafStep
end
