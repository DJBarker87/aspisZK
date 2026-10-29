import R1Z.PV_DL_DefaultNative
import R1Z.PV_DL_WrapLaw
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RDCD4_V237
open Aeneas Aeneas.Std Result PV_CBL_GenericArrayPower PV_CBL_LibraryShapes

/-- Explicit singleton value, kept symbolic through the named storage codec. -/
def literal : List U8 := List.replicate 64 0#u8

def observeBuffer (buffer : Buffer (Storage U8 6)) : List U8 × Nat :=
  (flatten 6 buffer.buffer,buffer.pos.val)

theorem buffer_literal : observeBuffer PV_DL_DefaultBuffer.initial=(literal,0) := by
  change (flatten 6 PV_DL_DefaultBuffer.zeroStorage,0)=(literal,0)
  rw [PV_DL_DefaultBuffer.bytes]
  rfl

/-- Relative pointer-end tests depend only on the public offset/length.
Native valid same-allocation pointer arithmetic remains the V370 boundary. -/
theorem address_independent (base offset length : Nat) :
    (base+offset=base+length) ↔ offset=length := by omega

/-- Full Result transport of the original Core::default parameter. The
byte-buffer constructor is fixed; no arbitrary buffer callback is added. -/
theorem complete {T : Type} (core : Result T) :
    (do let v ← PV_DL_DefaultBuffer.model core
        ok (PV_DL_WrapLaw.observe v)) =
    (do let c ← core
        let v ← PV_DL_Wrap.wrap_reference c
        ok (PV_DL_WrapLaw.observeReference v)) := by
  cases core with
  | ok c => simpa only [bind_tc_ok] using PV_DL_WrapLaw.source_reference c
  | fail e => rw [PV_DL_DefaultBuffer.failure];rfl
  | div => rw [PV_DL_DefaultBuffer.divergence];rfl

theorem result_literal {T : Type} (core : Result T) :
    (do let v ← PV_DL_DefaultBuffer.model core
        ok (v.core,observeBuffer v.buffer)) =
    (do let c ← core; ok (c,(literal,0))) := by
  cases core with
  | ok c =>
    rw [PV_DL_DefaultBuffer.success,bind_tc_ok]
    change ok (c,observeBuffer PV_DL_DefaultBuffer.initial)=ok (c,(literal,0))
    rw [buffer_literal]
  | fail e => rw [PV_DL_DefaultBuffer.failure];rfl
  | div => rw [PV_DL_DefaultBuffer.divergence];rfl

#check @PV_DL_DefaultNative.consumed
#print axioms PV_DL_DefaultNative.consumed
#print axioms buffer_literal
#print axioms address_independent
#print axioms complete
#print axioms result_literal
end R1Z.PV_RDCD4_V237
