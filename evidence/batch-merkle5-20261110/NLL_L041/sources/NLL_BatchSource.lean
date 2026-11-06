import NLL_ValuesReturning
import Port3_BatchStage
set_option autoImplicit false
noncomputable section
namespace NLL_BatchSource
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 NLL NLL_Parent
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

def roots (p : verifier.Prepared) (folded : NLL.Root) : Roots :=
 Port3_BatchStage.roots p folded

/-- Outer K019–K021 cut: exact Prepared.queries, BOTH Prepared roots and the
actual folded_root argument; no independently selected roots or child arrays. -/
def Invocation (H : Bytes → State) (proof : Slice U8) (p : verifier.Prepared)
 (folded : NLL.Root) (batch : Usize) (history : NLL.History) (out : NLL.Reply) : Prop :=
 NLL_Parent.Invocation H proof p.queries (roots p folded) batch history out

theorem source (H : Bytes → State) (proof : Slice U8) (p : verifier.Prepared)
 (folded : NLL.Root) (batch : Usize) :
 NKV_FRef.verifier.candidate.batch_merkle (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
   proof p folded batch ()=
 NKV_FRef.verifier.candidate.batch_merkle_values (NKV_ConcreteChildren.ops H) (NKV_ConcreteChildren.digest H)
   proof p.queries (roots p folded) batch () := by
 have h0 : Array.index_usize p.roots 0#usize=ok (Port3_BatchStage.root0 p) := by
   simp [Array.index_usize,Port3_BatchStage.root0,List.getElem?_eq_getElem]
 have h1 : Array.index_usize p.roots 1#usize=ok (Port3_BatchStage.root1 p) := by
   simp [Array.index_usize,Port3_BatchStage.root1,List.getElem?_eq_getElem]
 unfold NKV_FRef.verifier.candidate.batch_merkle
 rw [h0]
 simp only [bind_tc_ok]
 rw [h1]
 rfl

set_option pp.proofs false
#print source
#print axioms source
end NLL_BatchSource
end
