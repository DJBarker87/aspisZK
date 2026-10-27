import XRn_Join_Funs
open Aeneas Aeneas.Std Result ControlFlow
set_option autoImplicit false
namespace XRp_ReverseStep
abbrev Iter := core.iter.adapters.rev.Rev (core.slice.iter.IterMut U32)
abbrev Back := Iter → Iter
abbrev body := XRn_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body

def singleton (x : U32) : Iter := ⟨⟨⟨[x],by simp only [List.length_singleton]; decide⟩,0⟩⟩
def restored (s : Iter) : Result (List U32 × U64) := do
  let result ← body s id 0#u64
  match result with
  | .cont (next,back,rem) => ok ((back next).iter.slice.val,rem)
  | .done _ => fail .panic

/-- A single emitted reverse step restores the dividend limb, not its quotient. -/
theorem restores_P : restored (singleton 2147483647#u32) =
    ok ([2147483647#u32],0#u64) := by
  unfold restored body XRn_Join_Release.sampler.low_base_p_digits.closure_1.Insts.CoreOpsFunctionFnMutTupleUsizeU32.call_mut_loop.body
  unfold aspis_core.field.P
  rfl

#print axioms restores_P
end XRp_ReverseStep
