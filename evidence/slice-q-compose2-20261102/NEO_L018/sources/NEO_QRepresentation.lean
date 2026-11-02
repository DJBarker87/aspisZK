import NEO_QRef.Funs
import NEB_CheckedScalar
import NEB_ArrayRefs
import NEB_PureFrame
set_option autoImplicit false
namespace NEO_QRepresentation
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues

/-- Every raw fixed private-Q carrier, not only canonical coordinates. -/
theorem limbs (x : FIo_Native.fast_pairing.canonical.Q) :
    NEO_QRef.limbs x=FIo_Native.fast_pairing.canonical.Q.limbs x := rfl

/-- Complete raw constructor Result; neither acceptance nor canonicality is
assumed. The reference is independently extracted from the native comparison. -/
theorem from_limbs (x : Array U32 4#usize) :
    NEO_QRef.from_limbs x=FIo_Native.fast_pairing.canonical.Q.from_limbs x := by
  simp only [NEO_QRef.from_limbs,NEO_QRef.P,
    FIo_Native.fast_pairing.canonical.Q.from_limbs,FIo_Native.fast_pairing.canonical.P]

/-- Exact ordered low/high halves of the same eight-word owned carrier. -/
theorem from_wide (x : NE) :
    NEO_QRef.from_wide (NEB_ArrayRefs.wordsE x)=
      FIo_Native.fast_pairing.canonical.Q.from_wide x := by
  simp [NEO_QRef.from_wide,NEB_ArrayRefs.wordsE,
    FIo_Native.fast_pairing.canonical.Q.from_wide,
    FIo_Native.aspis_core.field.wide_exact.WideExact.to_limbs,Array.index_usize,Array.make]

/-- No canonical-input restriction on the public raw QM31 projection. -/
theorem limbs_of (x : NQ) :
    NEO_QRef.limbs_of (NEB_ArrayRefs.wordsQ x)=FIo_Native.fast_pairing.limbs_of x := rfl

theorem checked (x : NQ) :
    NEO_QRef.checked (NEB_ArrayRefs.wordsQ x)=FIo_Native.fast_pairing.checked_q x := by
  simp only [NEO_QRef.checked,from_limbs,FIo_Native.fast_pairing.checked_q,
    FIo_Native.fast_pairing.limbs_of,NEB_ArrayRefs.wordsQ,bind_tc_ok]

/-- Root purity is stated over its actual full Result, with rejected branches
retained. This does not supply a native mutable-carrier assumption. -/
theorem checked_frame {S Event : Type} (state : S) (x : NQ) :
    NEB_PureFrame.run (Event:=Event) state (NEO_QRef.checked (NEB_ArrayRefs.wordsQ x)) =
      NEB_PureFrame.run state (FIo_Native.fast_pairing.checked_q x) := by rw [checked]

#print axioms limbs
#print axioms from_limbs
#print axioms from_wide
#print axioms limbs_of
#print axioms checked
#print axioms checked_frame
end NEO_QRepresentation
