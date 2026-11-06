import NJS_BatchLeaf
import Port4B_ByteWord

set_option autoImplicit false
noncomputable section
namespace NKB_PaddingPredicate
open Aeneas Aeneas.Std Result AspisR1

def callback (chunk : Slice U8) : Result (Bool × Unit) :=
 NJS_Extract.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool.call_mut
   (NJS_RuntimeDigest.backend (fun _ => default)) () chunk

/-- The pinned std copy and unwrap return all eight bytes; no digest or opaque
operation is present in this emitted callback. Native mate: K015/K016. -/
theorem source (chunk : Slice U8) (size : chunk.val.length=8) :
 callback chunk=ok (core.num.U64.from_le_bytes (⟨chunk.val,size⟩ : Array U8 8#usize) != 0#u64,()) := by
 simp [callback,
   NJS_Extract.verifier.candidate.batch_tree.closure.Insts.CoreOpsFunctionFnMutTupleSharedSliceU8Bool.call_mut,
   core.array.TryFromArrayCopySlice.try_from,core.result.Result.unwrap,size,lift]

theorem zero_iff (word : Array U8 8#usize) :
 core.num.U64.from_le_bytes word=0#u64 ↔ ∀ b∈word.val,b=0#u8 := by
 constructor
 · intro zero b member
   exact Port4B_ByteWord.u64_zero word zero b member
 · intro all
   have eq : word=Array.repeat 8#usize 0#u8 := by
     apply Subtype.ext
     exact List.eq_replicate_iff.mpr ⟨word.property,all⟩
   rw [eq]
   rfl

/-- A first padding word with one nonzero byte is a concrete returning true
callback, not an allocator/syscall abort. Only this tiny eight-byte value is reduced. -/
theorem first_nonzero :
 callback (Array.to_slice (Array.make 8#usize [1#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8,0#u8]))=
   ok (true,()) := by
 rw [source _ (by rfl)]
 rfl

#print axioms source
#print axioms zero_iff
#print axioms first_nonzero
end NKB_PaddingPredicate
end
