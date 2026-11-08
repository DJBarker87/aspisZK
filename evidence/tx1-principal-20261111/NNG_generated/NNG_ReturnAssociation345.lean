import NNG_TryObservation345
import NNG_FirstNative345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_ReturnAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

theorem compare (a b : Usize) : (a != b)=(a.val != b.val) := by
 apply congrArg Bool.not
 apply Bool.eq_iff_iff.mpr
 simp only [beq_iff_eq]
 exact ⟨fun h=>congrArg UScalar.val h,fun h=>UScalar.eq_of_val_eq h⟩
#print axioms compare

theorem source (checkpoint : alloc.vec.Vec U8) (bytes : Slice U8) (env : RSL.Env) :
 observation NNG_ChildSource345.port (NNG_Events345.events env)
  (if alloc.vec.Vec.len checkpoint != Slice.len bytes then
   (pure (.Err .InvalidAccountData) : Code Ret) else pure (.Ok checkpoint))=
 NNG_Phases345.stepReturn (LIB_Carriers.bytes bytes).length (LIB_Carriers.bytes checkpoint.deref) := by
 rw [compare]
 have lengths : ((alloc.vec.Vec.len checkpoint).val != (Slice.len bytes).val) =
   ((LIB_Carriers.bytes checkpoint.deref).length != (LIB_Carriers.bytes bytes).length) := by
  simp only [NMS_R2N_RSLScalars.bytes_length]
  rfl
 rw [lengths]
 unfold NNG_Phases345.stepReturn
 split <;> rfl
#print axioms source
end AspisR1.NNG_ReturnAssociation345
