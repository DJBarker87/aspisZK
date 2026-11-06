import NLL_AbortInvocation
set_option autoImplicit false
noncomputable section
namespace NLL_AbortDomains
open Aeneas Aeneas.Std Result AspisR1Stage2 AspisR1 MultiproofConeRef NLL
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

theorem loop (H : Bytes → State) (proof : Slice U8) (root : NLL.Root) (batch : Nat)
 (kind lo n slot : Usize) (f : Frame) (events : List Event) (pending : Pending)
 (native : AbortLoop H proof root batch kind lo n slot f events pending)
 (smallN : n.val≤16) (limit : Nat) (cap : limit≤16) (pos : f.position.val≤n.val)
 (invariant : f.scratch.n.val+(n.val-f.position.val)≤limit) :
 pending.parent.scratch.n.val≤limit := by
 induction native with
 | leaf f more => exact Nat.le_trans (Nat.le_add_right _ _) invariant
 | verify f done well fits pad queries request state child => exact Nat.le_trans (Nat.le_add_right _ _) invariant
 | next f t more step events pending tail ih =>
   have small : f.scratch.n.val<16 := by change f.position.val<n.val at more;omega
   have exactStep:=step
   rw [MultiproofConeLeafContent.step_exact f.scratch _ _ small] at exactStep
   have countBound:=MultiproofConeLeafFold.next_bound f.scratch _ _ small t (Result.ok.inj exactStep)
   have inc:=Port3_Wrapping.increment f.position (by change f.position.val<n.val at more;omega)
   apply ih (by change (Usize.wrapping_add f.position 1#usize).val≤n.val;rw [inc];change f.position.val<n.val at more;omega)
     (by change t.n.val+(n.val-(Usize.wrapping_add f.position 1#usize).val)≤limit;rw [inc];change f.position.val<n.val at more;omega)

theorem source (H : Bytes → State) (proof : Slice U8) (raw : Array U32 22#usize)
 (root : NLL.Root) (batch kind : Usize) (idx : NLL.Indices) (val : NLL.Values)
 (events : List Event) (pending : Pending) (native : AbortInvocation H proof raw root batch kind idx val events pending) :
 pending.parent.scratch.n.val≤(if batch.val=0 then 10 else 12) := by
 rcases native with ⟨rest,rfl,nativeLoop⟩
 have zeroVal : (0#usize).val=0 := by scalar_tac
 have sizes:=NKB_KeyStream.positive batch.val
 have bound:=loop H proof root batch.val kind (NKB_KeyStream.lo batch.val)
   (NKB_KeyStream.count batch.val) _ _ rest pending nativeLoop (by omega) (NKB_KeyStream.count batch.val).val
   (by omega) (by change (0#usize).val≤_;rw [zeroVal];omega)
   (by change (0#usize).val+((NKB_KeyStream.count batch.val).val-(0#usize).val)≤_;rw [zeroVal];omega)
 have countValue : (NKB_KeyStream.count batch.val).val=(if batch.val=0 then 10 else 12) := by
   unfold NKB_KeyStream.count
   split <;> scalar_tac
 rw [countValue] at bound
 exact bound

set_option pp.proofs false
#print source
#print axioms loop
#print axioms source
end NLL_AbortDomains
end
