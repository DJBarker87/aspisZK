import NCV_ArrayRun
set_option autoImplicit false
namespace NDB_PrimaryBytes
open Aeneas Aeneas.Std Result

theorem value (b : Slice U8) (s : Usize) (target : Array U8 32#usize)
    (cap : b.val.length ≤ 768) (fit : s.val+32 ≤ b.val.length)
    (fields : ∀ k, k<32 → NCV_ZeroStep.byte b (s.val+k)=NCV_ArrayFrame.coord target k) :
    NCV_Reference.bytes32 b s=ok target := by
  have steps : ∀ a i, i.val<(32#usize).val → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.bytes32_loop.body b s a i=
        ok (.cont (a.set i (NCV_ArrayFrame.coord target i.val),next)) := by
    intro a i hi
    obtain ⟨next,nv,step⟩:=NCV_ByteStep.step b s i a cap fit hi
    exact ⟨next,nv,by simpa only [fields i.val hi] using step⟩
  unfold NCV_Reference.bytes32 NCV_Reference.bytes32_loop
  exact NCV_ArrayRun.run (fun (a,i)=>NCV_Reference.bytes32_loop.body b s a i)
    target id steps (fun a i h=>NCV_ByteStep.terminal b s i a h)
    _ 0#usize (by scalar_tac) (by intro j h; have hz : (0#usize).val=0 := rfl; rw [hz] at h; omega)
#print axioms value
end NDB_PrimaryBytes
