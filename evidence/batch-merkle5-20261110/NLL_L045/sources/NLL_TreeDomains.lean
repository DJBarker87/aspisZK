import NLL_LoopDomains
set_option autoImplicit false
noncomputable section
namespace NLL_TreeDomains
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem source (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (root : NLL.Root) (batch kind : Usize) (idx : NLL.Indices) (val : NLL.Values)
 (events : List Event) (out : NLL.Answer) (native : NLL.Invocation H proof raw root batch kind idx val events out)
 (nodes : Slice U8) (count : Nat) (before : reference.Scratch)
 (queries : List (NJP_RowModel.Request × NJP_RowModel.Digest)) (answer : Bool × NJP_RowModel.Scratch)
 (entered : Event.verify nodes count before queries answer∈events) :
 0<before.n.val ∧ before.n.val≤(if batch.val=0 then 10 else 12) ∧
 OraclePortFrozenOrder.wellFormed (NJV_UnitDomain.keys before) := by
 rcases native with ⟨rest,rfl,loop⟩
 have member : Event.verify nodes count before queries answer∈rest := by
   simp only [List.mem_cons] at entered
   rcases entered with bad|good
   · cases bad
   · exact good
 have zeroVal : (0#usize).val=0 := by scalar_tac
 have sizes:=NKB_KeyStream.positive batch.val
 have bound:=NLL_LoopDomains.source H proof root batch.val kind (NKB_KeyStream.lo batch.val)
   (NKB_KeyStream.count batch.val) _ _ rest out loop (by omega) (NKB_KeyStream.count batch.val).val
   (by omega) (by change (0#usize).val≤_;rw [zeroVal];omega)
   (by change (0#usize).val+((NKB_KeyStream.count batch.val).val-(0#usize).val)≤_;rw [zeroVal];omega)
   nodes count before queries answer member
 have live : 0<before.n.val := by
   have nonempty:=bound.2.1
   by_contra bad
   have zero : before.n.val=0 := by omega
   have length:=NJV_UnitDomain.key_length before
   rw [zero] at length
   exact nonempty (List.length_eq_zero_iff.mp length)
 have countValue : (NKB_KeyStream.count batch.val).val=(if batch.val=0 then 10 else 12) := by
   unfold NKB_KeyStream.count
   split <;> scalar_tac
 exact ⟨live,by rw [countValue] at bound;exact bound.1,bound.2⟩

set_option pp.proofs false
#print source
#print axioms source
end NLL_TreeDomains
end
