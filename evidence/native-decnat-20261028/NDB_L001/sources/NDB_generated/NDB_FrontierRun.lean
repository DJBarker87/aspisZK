import NCV_FrontierStep
set_option autoImplicit false
namespace NDB_FrontierRun
open Aeneas Aeneas.Std Result
abbrev Row := Array U32 8#usize
abbrev Frontier := Array Row 20#usize
local instance : Inhabited (Array U32 8#usize) := ⟨Array.repeat 8#usize 0#u32⟩

theorem value (tree : Slice U8) (next : U64) (target : Frontier)
    (fields : ∀ i : Usize, i.val<20 → ∀ addr : Usize, addr.val=48+32*i.val →
      NCV_CastRef.digest tree addr=ok (.Ok (NCV_ArrayFrame.coord target i.val)))
    (guards : ∀ i : Usize, i.val<20 → ∃ tag : U64, next >>> i=ok tag ∧
      (tag &&& 1#u64=0#u64 → NCV_ArrayFrame.coord target i.val=NCV_ArrayFrame.coord NCV_CastRef.EMPTY i.val)) :
    NCV_CastRef.decode_frontier tree next=ok (.Ok target) := by
  have steps : ∀ a (i : Usize), i.val<(20#usize).val → ∃ successor : Usize,
      successor.val=i.val+1 ∧ NCV_CastRef.decode_frontier_loop.body tree next a i=
        ok (.cont (a.set i (NCV_ArrayFrame.coord target i.val),successor)) := by
    intro a i hi
    obtain ⟨tag,shift,empty⟩:=guards i hi
    exact NCV_FrontierStep.step tree next a i _ tag hi (fields i hi) shift empty
  unfold NCV_CastRef.decode_frontier NCV_CastRef.decode_frontier_loop
  dsimp only
  exact NCV_ArrayRun.run (fun (a,i)=>NCV_CastRef.decode_frontier_loop.body tree next a i)
    target core.result.Result.Ok steps (fun a i h=>NCV_FrontierStep.terminal tree next a i h)
    _ 0#usize (by scalar_tac) (by
      change NCV_ArrayFrame.Prefix _ target 0
      intro j h
      omega)

#print axioms value
end NDB_FrontierRun
