import Lean
import NFY_Part032
import NGE_NEL_FrontierGeometry
import NFY_Part030
import NFY_Part023

set_option autoImplicit false
noncomputable section
namespace NGE_NEM_EncoderFrame
open Aeneas Aeneas.Std Result AspisR1TerminalDecoder AspisR1.S2K

theorem frontier_next (rows : Array (Array U32 8#usize) 20#usize)
    (i : Usize) (bound : i.val < 20) :
    LoopStep.next (Iterator.cursor rows i) = ok
      (some (i,rows.val[i.val]'(by have := rows.property; change rows.val.length=20 at this; omega)),
       Iterator.cursor rows (Usize.ofNatCore (i.val+1) (by scalar_tac))) :=
  Iterator.next_row rows i bound

/-- The same emitted native iteration, actual node, arbitrary original slice,
and exact global byte frame. No independently selected child buffer occurs. -/
theorem live_step_and_bytes (rows : Array (Array U32 8#usize) 20#usize)
    (i : Usize) (bound : i.val < 20) (out : Slice U8) (size : out.length = 800) :
    ∃ next, ∃ after : Slice U8,
      NFY_NBK_LiveStep.body (Iterator.cursor rows i) out = ok (.cont (next,after)) ∧
      ∀ k : Nat, after.val[k]? = KMX_CopyMeaning.loop
        (fun j => (DigestBytes.bytes
          (rows.val[i.val]'(by have := rows.property; change rows.val.length=20 at this; omega))).val[j-(160+32*i.val)]?)
        (fun j => out.val[j]?) (160+32*i.val) 32 k := by
  let node := rows.val[i.val]'(by have := rows.property; change rows.val.length=20 at this; omega)
  refine ⟨_,_,NFY_NBK_LiveStep.body_write _ _ out i node (DigestBytes.bytes node)
    (Iterator.next_row rows i bound) bound size (DigestBytes.exact node),?_⟩
  intro k
  have len : (DigestBytes.bytes node).to_slice.length = 32 := (DigestBytes.bytes node).property
  have fits : 160+32*i.val+32 ≤ out.length := by rw [size]; omega
  have same := (NFY_NEL_SliceCopyLaw.loop_binding out (DigestBytes.bytes node).to_slice
    (160+32*i.val) k (by rw [len]; exact fits)).symm
  rw [len] at same
  simpa only [Array.to_slice] using same

theorem after_step_and_bytes (rows : Array (Array U32 8#usize) 20#usize)
    (i : Usize) (bound : i.val < 20) (out : Array U8 688#usize) :
    ∃ next, ∃ after : Array U8 688#usize,
      LoopStep.body (Iterator.cursor rows i) out = ok (.cont (next,after)) ∧
      ∀ k : Nat, after.val[k]? = KMX_CopyMeaning.loop
        (fun j => (DigestBytes.bytes
          (rows.val[i.val]'(by have := rows.property; change rows.val.length=20 at this; omega))).val[j-(48+32*i.val)]?)
        (fun j => out.val[j]?) (48+32*i.val) 32 k := by
  let node := rows.val[i.val]'(by have := rows.property; change rows.val.length=20 at this; omega)
  refine ⟨_,_,LoopStep.body_write _ _ out i node (DigestBytes.bytes node)
    (Iterator.next_row rows i bound) bound (DigestBytes.exact node),?_⟩
  intro k
  exact (NFY_NEL_CopyArrayLaw.loop_binding out (DigestBytes.bytes node)
    (48+32*i.val) k (by change 48+32*i.val+32 ≤ 688; omega)).symm

/-- Actual fill realization is a separately pinned native intrinsic check. -/
theorem fill_value (out : Slice U8) :
    core.slice.Slice.fill core.clone.CloneU8 out 0#u8 = ok (NFY_NBK_Fill.value out 0#u8) :=
  NFY_NBK_Fill.source out 0#u8

theorem live_value_and_frame {State : Type} (s : NFY_NBH_LiveValidator.Snapshot)
    (out : Slice U8) (state : State) :
    (pool_v1.pair_tree_profile.encode_pool_v1_pair_live_snapshot_v1 s out,state) =
      (NFY_NBN_EncoderSummary.live atomic_statement.encode_digest_canonical s out,state) := by
  rw [NFY_NED_SubtreeComposition.live_encode]

theorem after_value_and_frame {State : Type} (a : NFY_NBH_Validators.Afterstate) (state : State) :
    (pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 a,state) =
      (NFY_NBN_EncoderSummary.after atomic_statement.encode_digest_canonical a,state) := by
  rw [NFY_NED_SubtreeComposition.after_encode]

#print axioms frontier_next
#print axioms live_step_and_bytes
#print axioms after_step_and_bytes
#print axioms fill_value
#print axioms live_value_and_frame
#print axioms after_value_and_frame
end NGE_NEM_EncoderFrame

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
