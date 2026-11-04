import Lean
import NFY_Part032

set_option autoImplicit false
noncomputable section
namespace NGE_NEM_ArraySnapshotView
open Aeneas Aeneas.Std Result

/-- The fixed view covers EVERY possible original slice poststate, with no
byte restriction, fresh native object, or independent execution witness. -/
theorem cover (post : Slice U8) (size : post.length = 800) :
    ∃ array : Array U8 800#usize, array.to_slice = post := by
  refine ⟨⟨post.val,size⟩,?_⟩
  apply Subtype.ext
  rfl

theorem poststate (out : Slice U8) (size : out.length = 1520)
    (post : Array U8 800#usize) (k : Nat) :
    (out.setSlice! 32 post.val).val[k]? =
      if 32 ≤ k ∧ k < 832 then post.val[k-32]? else out.val[k]? := by
  have len : post.to_slice.length = 800 := post.property
  simpa only [Array.to_slice] using NFY_NEM_SnapshotBorrow.poststate out post.to_slice size len k

#print axioms cover
#print axioms poststate
end NGE_NEM_ArraySnapshotView

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
