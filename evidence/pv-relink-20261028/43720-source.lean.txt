import R1Z.PV_AL_SplitSelected
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_AL_SplitBridge
open ProverRwFull PV_AL_SplitNativeShape PV_CBL_GenericArrayPower
set_option autoImplicit false

def observe (base : ExternalTypes) (ops : @ExternalFuns (Types base)) (v : Slice U8) :
    Result (List U8 × List U8) := do
  let (blocks,tail) ← @ExternalFuns.op209 (Types base) (PV_AL_SplitSelected.selected base ops)
    (Size base 6) (Storage U8 6) (nativeTrait base ops 6) v
  ok ((blocks.val.map PV_AL_SplitCarrier.decodeBlock).flatten,tail.val)

/-- Complete Result/value link for every input slice, without a length bound
or a source-equality premise. The same native 64-byte storage is consumed. -/
theorem source_reference (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (v : Slice U8) : observe base ops v=PV_AL_SplitObservation.observe v 64#usize := by
  rw [PV_AL_SplitObservation.positive v 64#usize (by decide)]
  simp only [observe,PV_AL_SplitSelected.native_callback,bind_tc_ok]
  exact congrArg Result.ok (Prod.ext
    (PV_AL_SplitCarrier.block_bytes (Size base 6) v) (PV_AL_SplitCarrier.tail_bytes v))

theorem consumed_reassembles (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (v : Slice U8) :
    letI : ExternalTypes := Types base
    ∃ (blocks : Slice (PV_AL_SplitCarrier.Block (Size base 6))) (tail : Slice U8),
      (@block_buffer.Eager.Insts.Block_bufferSealedSealed (Types base)
        (PV_AL_SplitSelected.selected base ops)).split_blocks (nativeTrait base ops 6) v=
        ok (blocks,tail) ∧
      (blocks.val.map PV_AL_SplitCarrier.decodeBlock).flatten ++ tail.val=v.val := by
  letI : ExternalTypes := Types base
  refine ⟨PV_AL_SplitCarrier.blockSlice (Size base 6) v,PV_AL_SplitCarrier.tailSlice v,
    PV_AL_SplitSelected.consumed base ops v,?_⟩
  rw [PV_AL_SplitCarrier.block_bytes,PV_AL_SplitCarrier.tail_bytes]
  exact List.take_append_drop _ _

#print axioms observe
#print axioms source_reference
#print axioms consumed_reassembles
end R1Z.PV_AL_SplitBridge
