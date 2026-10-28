import R1Z.PV_DL_UpdateCarrier
import R1Z.PV_DL_DefaultCallback
import R1Z.PV_AL_SplitNativeShape
open Aeneas Aeneas.Std Result ProverRwFull
noncomputable section
namespace R1Z.PV_DL_UpdateSelected
open PV_CBL_LibraryShapes PV_CBL_GenericArrayPower
set_option autoImplicit false
abbrev Types := PV_CBL_LibraryShapeTypes.selectedTypes

def dispatch {T N A0 A1 : Type}
    (update : T → Slice (GenericArray U8 N A1) → Result T)
    (fallback : Wrapper T A0 → Slice U8 → Result (Wrapper T A0))
    (self : Wrapper T A0) (input : Slice U8) : Result (Wrapper T A0) := by
  classical
  by_cases h0 : A0=Storage U8 6
  · subst A0
    by_cases h1 : A1=Storage U8 6
    · subst A1;exact PV_DL_UpdateCarrier.callback update self input
    · exact fallback self input
  · exact fallback self input

theorem dispatch_source {T N : Type} (update : T → PV_DL_UpdateCarrier.Blocks N → Result T)
    (fallback : Wrapper T (Storage U8 6) → Slice U8 → Result (Wrapper T (Storage U8 6)))
    (self : Wrapper T (Storage U8 6)) (input : Slice U8) :
    dispatch update fallback self input=PV_DL_UpdateCarrier.value update self input := by
  classical
  simp only [dispatch]
  rw [dif_pos True.intro,dif_pos True.intro]
  exact PV_DL_UpdateCarrier.complete update self input

def updater (base : ExternalTypes) {T N A : Type}
    (uc : @digest.core_api.UpdateCore (Types base) T N A) :
    T → Slice (GenericArray U8 N A) → Result T :=
  @digest.core_api.UpdateCore.update_blocks (Types base) T N A uc

/-- Dictionary selection is nominally erased in the emitted types: both
Eager and Lazy markers are Unit. Compare the complete original dictionary,
then discharge the test at the actual generated Eager constructor. -/
def kindDispatch (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    {K R : Type} (kind : @block_buffer.BufferKind (Types base) K)
    (accepted fallback : R) : R := by
  classical
  by_cases hk : K=block_buffer.Eager
  · subst K
    by_cases hc : kind=@block_buffer.Eager.Insts.Block_bufferBufferKind (Types base) ops
    · exact accepted
    · exact fallback
  · exact fallback

theorem native_kind (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    {R : Type} (accepted fallback : R) :
    kindDispatch base ops (@block_buffer.Eager.Insts.Block_bufferBufferKind (Types base) ops)
      accepted fallback=accepted := by
  classical
  simp [kindDispatch]

def bufferKind (base : ExternalTypes) (ops : @ExternalFuns (Types base)) (T : Type) :
    @digest.core_api.BufferKindUser (Types base) T block_buffer.Eager
      (PV_AL_SplitNativeShape.Size base 6) (Storage U8 6) := by
  letI : ExternalTypes := Types base
  exact ⟨⟨PV_AL_SplitNativeShape.nativeTrait base ops 6⟩,
    @block_buffer.Eager.Insts.Block_bufferBufferKind (Types base) ops⟩

@[reducible] def selected (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @ExternalFuns (Types base) :=
  letI : ExternalTypes := Types base
  {ops with
    op216 := fun bk uc less nz =>
      kindDispatch base ops bk.block_bufferBufferKindInst
        (dispatch (updater base uc) (ops.op216 bk uc less nz))
        (ops.op216 bk uc less nz)}

theorem retained_kind (base : ExternalTypes) (ops : @ExternalFuns (Types base)) :
    @block_buffer.Eager.Insts.Block_bufferBufferKind (Types base) (selected base ops)=
      @block_buffer.Eager.Insts.Block_bufferBufferKind (Types base) ops := rfl

theorem selected_native (base : ExternalTypes) (ops : @ExternalFuns (Types base))
    {T N1 O : Type}
    (uc : @digest.core_api.UpdateCore (Types base) T N1 (Storage U8 6))
    (less : typenum.type_operators.IsLess (PV_AL_SplitNativeShape.Size base 6)
      (PV_DL_DefaultCallback.Limit base) O)
    (nz : typenum.marker_traits.NonZero O)
    (self : Wrapper T (Storage U8 6)) (input : Slice U8) :
    @ExternalFuns.op216 (Types base) (selected base ops)
      T block_buffer.Eager (PV_AL_SplitNativeShape.Size base 6) (Storage U8 6)
      N1 (Storage U8 6) O (bufferKind base ops T) uc less nz self input=
      PV_DL_UpdateCarrier.value (updater base uc) self input := by
  let fallback := @ExternalFuns.op216 (Types base) ops T block_buffer.Eager
    (PV_AL_SplitNativeShape.Size base 6) (Storage U8 6) N1 (Storage U8 6) O
    (bufferKind base ops T) uc less nz
  change (@kindDispatch base ops block_buffer.Eager
    (Wrapper T (Storage U8 6) → Slice U8 → Result (Wrapper T (Storage U8 6)))
    (@block_buffer.Eager.Insts.Block_bufferBufferKind (Types base) ops)
    (dispatch (updater base uc) fallback) fallback) self input=_
  rw [native_kind]
  exact dispatch_source (updater base uc) fallback self input

#print axioms Types
#print axioms dispatch
#print axioms dispatch_source
#print axioms updater
#print axioms kindDispatch
#print axioms native_kind
#print axioms bufferKind
#print axioms selected
#print axioms retained_kind
#print axioms selected_native
end R1Z.PV_DL_UpdateSelected
