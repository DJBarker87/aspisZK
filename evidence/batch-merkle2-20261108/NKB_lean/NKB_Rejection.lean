import NJS_BatchLeaf
import NJS_Slot
import NJV_TX2

set_option autoImplicit false
noncomputable section
namespace NKB_Rejection
open Aeneas Aeneas.Std Result ControlFlow

/-- Unentered opaque slots deliberately fail; the rejected-count path never
uses them. This diagnostic does not supply a deployed operation dictionary. -/
def terminal (proof : Slice U8) (root : Array U8 32#usize)
    (idx : Array U32 16#usize) (val : Array (Array U8 32#usize) 16#usize) :=
 NJS_Extract.verifier.candidate.batch_tree_loop.body
   (fun _ _ _ _ => fail .panic) (ok 113#u8) (ok 241#u8) NJS_BatchLeaf.privateLeaf
   (fun _ => fail .panic) (fun _ _ _ _ _ _ _ _ => fail .panic)
   (fun _ _ => ok none) (NJS_RuntimeDigest.backend (fun _ => default))
   proof root 0#usize () 0#usize 0#usize 0#usize
   (Array.repeat 16#usize 0#u64) idx val 0#usize 0#usize

/-- The reused emission loses the Rust Err(Merkle) at an empty-count terminal.
This is a local diagnostic; no reachability at the positive batch caller is claimed. -/
theorem count_none (proof : Slice U8) (root : Array U8 32#usize)
    (idx : Array U32 16#usize) (val : Array (Array U8 32#usize) 16#usize) :
 terminal proof root idx val = ok (done (idx,val,none)) := by
 unfold terminal NJS_Extract.verifier.candidate.batch_tree_loop.body
 simp only [lt_self_iff_false,if_false]
 simp only [core.array.Array.index,core.ops.index.IndexSlice]
 simp only [core.slice.index.Slice.index,core.slice.index.SliceIndexRangeToUsizeSlice.index,
   show (0#usize).val≤idx.to_slice.length from Nat.zero_le _,if_true,bind_tc_ok,
   NJS_Extract.core.option.Option.ok_or,core.result.Result.Insts.CoreOpsTry.branch,
   core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
   core.convert.FromSame,bind_tc_ok]

 split
 · rfl
 · rename_i impossible
   exact (impossible (by scalar_tac)).elim


/-- The wrapper's exact pending-return boundary, also present in Port3. -/
def boundary (idx : Array U32 16#usize) (val : Array (Array U8 32#usize) 16#usize)
    (pending : Option (core.result.Result Unit NJS_Extract.verifier.Error)) :
    Result (core.result.Result Unit NJS_Extract.verifier.Error ×
      Array U32 16#usize × Array (Array U8 32#usize) 16#usize) :=
 match pending with
 | none => fail .panic
 | some r => ok (r,idx,val)

theorem lost_error (idx : Array U32 16#usize) (val : Array (Array U8 32#usize) 16#usize)
    (error : NJS_Extract.verifier.Error) :
 boundary idx val none ≠ ok (.Err error,idx,val) := by intro impossible;cases impossible

set_option pp.proofs false
#print lost_error
#print axioms lost_error

#print count_none
#print axioms count_none
end NKB_Rejection
end
