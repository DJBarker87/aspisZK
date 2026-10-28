import NDB_PrimaryDigestStep
set_option autoImplicit false
namespace NDB_PrimaryDigestRun
open Aeneas Aeneas.Std Result

theorem value (b : Slice U8) (s : Usize) (target : Array U32 8#usize)
    (read : Nat → Array U8 4#usize) (cap : b.val.length ≤ 768)
    (fit : s.val+32 ≤ b.val.length)
    (fields : ∀ k, k<8 → (b.val.drop (s.val+4*k)).take 4=(read k).val)
    (values : ∀ k, k<8 → core.num.U32.from_le_bytes (read k)=NCV_ArrayFrame.coord target k)
    (canonical : ∀ k, k<8 → (core.num.U32.from_le_bytes (read k)).val<2147483647) :
    NCV_Reference.digest b s=ok (.Ok target) := by
  have steps : ∀ a i, i.val<(8#usize).val → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.digest_loop.body b s a i=
        ok (.cont (a.set i (NCV_ArrayFrame.coord target i.val),next)) := by
    intro a i hi
    obtain ⟨next,nv,step⟩:=NDB_PrimaryDigestStep.step b s i a (read i.val) cap fit hi
      (fields i.val hi) (canonical i.val hi)
    exact ⟨next,nv,by simpa only [values i.val hi] using step⟩
  have call : NCV_Reference.digest_loop b s (Array.repeat 8#usize 0#u32) 0#usize=ok (target,none) := by
    unfold NCV_Reference.digest_loop
    exact NCV_ArrayRun.run (fun (a,i)=>NCV_Reference.digest_loop.body b s a i)
      target (fun a=>(a,none)) steps (fun a i h=>NDB_PrimaryDigestStep.terminal b s i a h)
      _ 0#usize (by scalar_tac) (by intro j h; have hz : (0#usize).val=0 := rfl; rw [hz] at h; omega)
  unfold NCV_Reference.digest
  dsimp only
  rw [call]
  rfl

#print axioms value
end NDB_PrimaryDigestRun
