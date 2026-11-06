import NLL_Invocation
set_option autoImplicit false
noncomputable section
namespace NLL_EntryStep
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Entry installs the retained full native key-producer/sort cut at SAME
arguments. The selected concrete array itself, not an assumed stream, supplies
all following key reads and loop bounds. -/
theorem source (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (root : NLL.Root) (batch kind : Usize) (hb : batch.val<2) (hk : kind.val<3)
 (canonical : ∀ j,j<22 → raw.val[j]!.val<262144) (idx : NLL.Indices) (val : NLL.Values) :
 (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch.val kind.val).length=
   (NKB_KeyStream.count batch.val).val ∧
 Port4B_LeafLoop.KeyStream (Port4B_KeyInstall.queries raw) batch.val kind.val
   (entryKeys H raw batch.val kind) 0#usize
   (OraclePortFrozenOrder.sortedPositions (Port4B_KeyInstall.queries raw) batch.val kind.val) ∧
 NKV_FRef.verifier.candidate.batch_tree (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
   proof raw root batch kind idx val ()=
 (NKV_FRef.verifier.candidate.batch_tree_loop (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
   proof root kind idx val () (NKB_KeyStream.lo batch.val) (NKB_KeyStream.count batch.val)
   (Usize.wrapping_add (Usize.wrapping_mul 3#usize batch) kind) (entryKeys H raw batch.val kind)
     0#usize 0#usize >>= NKV_ReturnBoundary.returned) := by
 obtain ⟨keys,run,length,stream⟩:=NKV_KeyInvocation.source H raw batch.val kind hb hk canonical
 have selected : entryKeys H raw batch.val kind=keys := by unfold entryKeys;rw [run]
 rw [selected]
 refine ⟨length,stream,?_⟩
 have keyRead := NKB_KeyStream.built raw batch.val kind hk hb canonical
 have sortRead : (NKV_ConcreteChildren.ops H).op5 (Port4B_KeyInstall.keyArray raw batch.val kind.val)
     (NKB_KeyStream.count batch.val)=ok keys := by rw [keyRead] at run;exact run
 have notzero : ¬(1#usize=0#usize) := by scalar_tac
 have batches : batch=0#usize ∨ batch=1#usize := by
   by_cases zero : batch.val=0
   · exact Or.inl (UScalar.eq_of_val_eq zero)
   · exact Or.inr (UScalar.eq_of_val_eq (by change batch.val=1;omega))
 have natnz : ¬(1:Nat)=0 := by omega
 have zeroVal : (0#usize).val=0 := by scalar_tac
 have oneVal : (1#usize).val=1 := by scalar_tac
 rcases batches with rfl|rfl
 all_goals
   unfold NKV_FRef.verifier.candidate.batch_tree
   simp only [NKV_ConcreteChildren.ops,lift,bind_tc_ok,↓reduceIte,Aeneas.Std.uncurry,notzero,if_false,
     NKV_BatchGeometry.span0,NKV_BatchGeometry.span1,NKB_KeyStream.lo,NKB_KeyStream.count,
     zeroVal,oneVal,natnz] at keyRead sortRead ⊢
   rw [keyRead]
   simp only [bind_tc_ok]
   rw [sortRead]
   simp only [bind_tc_ok]
   rfl

set_option pp.proofs false
#print source
#print axioms source
end NLL_EntryStep
end
