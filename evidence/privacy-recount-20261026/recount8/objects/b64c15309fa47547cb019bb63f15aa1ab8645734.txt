import R1Z.PV_AL_SplitNativeShape
import R1Z.PV_AL_SplitCarrier
import R1Z.PV_AL_SplitObservation
open Aeneas Aeneas.Std Result
noncomputable section
namespace R1Z.PV_AL_SplitSelected
open ProverRwFull PV_CBL_GenericArrayPower PV_AL_SplitNativeShape
set_option autoImplicit false

/-- Typed dispatch is proved on explicit storage before dictionary installation. -/
def dispatch {N A : Type} (size : Result Usize) (v : Slice U8)
    (fallback : Unit → Result (Slice (PV_CBL_LibraryShapes.GenericArray U8 N A) × Slice U8)) :
    Result (Slice (PV_CBL_LibraryShapes.GenericArray U8 N A) × Slice U8) := by
  classical
  by_cases hA : A=Storage U8 6
  · subst A
    exact if size=ok 64#usize then PV_AL_SplitCarrier.reference N v else fallback ()
  · exact fallback ()

theorem dispatch_source (N : Type) (size : Result Usize) (v : Slice U8)
    (fallback : Unit → Result (Slice (PV_AL_SplitCarrier.Block N) × Slice U8))
    (hs : size=ok 64#usize) : dispatch size v fallback=PV_AL_SplitCarrier.reference N v := by
  classical
  simp only [dispatch,hs,if_true]
  exact dif_pos True.intro

/-- Install the selected native storage/size callback and concrete size constants. -/
@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  let ops' := PV_AL_TypenumSize.selected base ops
  {ops' with
    op209 := fun {N} {A} cls v =>
      dispatch cls.typenummarker_traitsUnsignedInst.USIZE v (fun _ => ops'.op209 cls v)}

theorem callback (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (N : Type) (trait : generic_array.ArrayLength N U8 (Storage U8 6))
    (hs : trait.typenummarker_traitsUnsignedInst.USIZE=ok 64#usize) (v : Slice U8) :
    letI : ExternalTypes := Types base
    @ExternalFuns.op209 (Types base) (selected base ops) N (Storage U8 6) trait v=PV_AL_SplitCarrier.reference N v :=
  dispatch_source N trait.typenummarker_traitsUnsignedInst.USIZE v _ hs

theorem native_callback (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (v : Slice U8) :
    letI : ExternalTypes := Types base
    @ExternalFuns.op209 (Types base) (selected base ops) (Size base 6) (Storage U8 6) (nativeTrait base ops 6) v=
      ok (PV_AL_SplitCarrier.blockSlice (Size base 6) v,PV_AL_SplitCarrier.tailSlice v) :=
  callback base ops (Size base 6) (nativeTrait base ops 6) (native_size base ops) v

theorem consumed (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    (v : Slice U8) :
    letI : ExternalTypes := Types base
    (@block_buffer.Eager.Insts.Block_bufferSealedSealed (Types base)
      (selected base ops)).split_blocks (nativeTrait base ops 6) v=
      ok (PV_AL_SplitCarrier.blockSlice (Size base 6) v,PV_AL_SplitCarrier.tailSlice v) :=
  native_callback base ops v

#print axioms dispatch
#print axioms dispatch_source
#print axioms selected
#print axioms callback
#print axioms native_callback
#print axioms consumed
end R1Z.PV_AL_SplitSelected
