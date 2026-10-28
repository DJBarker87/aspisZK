import JHu_SequenceStep
set_option autoImplicit false
namespace AspisR1.JHu_SequenceRun
open Aeneas Aeneas.Std Result AspisR1

theorem value (b : Slice U8) (s : Usize) (target : Array U64 8#usize)
    (read : Nat → Array U8 8#usize) (cap : b.val.length ≤ 768)
    (fit : s.val+64 ≤ b.val.length)
    (fields : ∀ k, k<8 → (b.val.drop (s.val+8*k)).take 8=(read k).val)
    (values : ∀ k, k<8 → core.num.U64.from_le_bytes (read k)=NCV_ArrayFrame.coord target k) :
    NCV_Reference.sequences b s=ok target := by
  have steps : ∀ a i, i.val<(8#usize).val → ∃ next : Usize, next.val=i.val+1 ∧
      NCV_Reference.sequences_loop.body b s a i=
        ok (.cont (a.set i (NCV_ArrayFrame.coord target i.val),next)) := by
    intro a i hi
    obtain ⟨next,nv,step⟩:=JHu_SequenceStep.step b s i a (read i.val) cap fit hi (fields i.val hi)
    exact ⟨next,nv,by simpa only [values i.val hi] using step⟩
  unfold NCV_Reference.sequences NCV_Reference.sequences_loop
  exact NCV_ArrayRun.run (fun (a,i)=>NCV_Reference.sequences_loop.body b s a i)
    target id steps (fun a i h=>JHu_SequenceStep.terminal b s i a h)
    _ 0#usize (by scalar_tac) (by intro j h; have hz : (0#usize).val=0 := rfl; rw [hz] at h; omega)

#print axioms value
end AspisR1.JHu_SequenceRun
