import NNG_Tree345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_BoundsAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

/-- Only the frozen scalar constants are reduced: no proof buffer or child
computation is evaluated. -/
theorem source {W : Type} (s : ProofData W) (env : RSL.Env) (events : Event → List RSL.Event) :
 observation NNG_ChildSource345.port events (NNG_TreeTail345.bounds (NNG_Calls345.calls env) s)=
 observation NNG_ChildSource345.port events (NNG_TreeTail345.tail (NNG_Calls345.calls env) ⟨s,688#usize,58295#usize⟩) := by
 have add : Usize.checked_add 688#usize 57607#usize=some 58295#usize := by
  unfold Usize.checked_add core.num.checked_add_UScalar
  scalar_tac
 unfold NNG_TreeTail345.bounds
 change observation _ _ (do
  let sum ← (liftM (Aeneas.Std.lift (Usize.checked_add 688#usize 57607#usize)) : Code _)
  NNG_TreeBase345.tryCode (NMT_stage1_owned.core.option.Option.ok_or sum
   NMT_stage1_owned.solana_program_error.ProgramError.InvalidAccountData)
   (fun end_=>NNG_TreeTail345.tail (NNG_Calls345.calls env) ⟨s,688#usize,end_⟩)) = _
 rw [add]
 rfl
#print axioms source
end AspisR1.NNG_BoundsAssociation345
