import JHu_FrontierStep
set_option autoImplicit false
namespace AspisR1.JHu_FrontierRun
open Aeneas Aeneas.Std Result
local instance : Inhabited (Array U32 (Usize.ofNatCore 8 (by scalar_tac))) := ⟨Array.repeat (Usize.ofNatCore 8 (by scalar_tac)) 0#u32⟩

theorem source (tree : Slice U8) (next : U64) (target : Array (Array U32 (Usize.ofNatCore 8 (by scalar_tac))) 20#usize)
    (reads : ∀ (i addr : Usize), i.val<20 → addr.val=48+32*i.val →
      NCV_Reference.digest tree addr=ok (.Ok (NCV_ArrayFrame.coord target i.val)))
    (bits : ∀ i : Usize, i.val<20 → ∃ tag : U64, next >>> i=ok tag ∧
      (tag &&& 1#u64=0#u64 → NCV_ArrayFrame.coord target i.val=NCV_ArrayFrame.coord NCV_Reference.EMPTY i.val)) :
    NCV_Reference.decode_frontier tree next=ok (.Ok target) := by
  have steps : ∀ (a : Array (Array U32 (Usize.ofNatCore 8 (by scalar_tac))) 20#usize) (i : Usize), i.val<(20#usize).val →
      ∃ successor : Usize, successor.val=i.val+1 ∧
        NCV_Reference.decode_frontier_loop.body tree next a i=
          ok (.cont (a.set i (NCV_ArrayFrame.coord target i.val),successor)) := by
    intro a i hi
    obtain ⟨tag,shift,empty⟩:=bits i hi
    exact JHu_FrontierStep.step tree next a i _ tag hi (reads i · hi) shift empty
  unfold NCV_Reference.decode_frontier NCV_Reference.decode_frontier_loop
  exact NCV_ArrayRun.run (n:=20#usize)
    (fun (a,i)=>NCV_Reference.decode_frontier_loop.body tree next a i)
    target core.result.Result.Ok steps (fun a i h=>JHu_FrontierStep.terminal tree next a i h)
    _ 0#usize (by scalar_tac) (by intro j h; have hz : (0#usize).val=0 := rfl; rw [hz] at h; omega)
#print axioms source
end AspisR1.JHu_FrontierRun
