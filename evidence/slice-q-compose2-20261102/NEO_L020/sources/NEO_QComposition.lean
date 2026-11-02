import NEO_QRepresentation
set_option autoImplicit false
namespace NEO_QComposition
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev Q := FIo_Native.fast_pairing.canonical.Q

/-- The private Q carrier is exactly the same four raw words; no canonicality
or successful parse is required to identify a returned value. -/
theorem carrier (x y : Q) (h : x=y) : x=y := h

theorem limbs_frame {S Event : Type} (s : S) (x : Q) :
 NEB_PureFrame.run (Event:=Event) s (NEO_QRef.limbs x) =
 NEB_PureFrame.run s (FIo_Native.fast_pairing.canonical.Q.limbs x) := by
 rw [NEO_QRepresentation.limbs]

theorem constructor_frame {S Event : Type} (s : S) (x : Array U32 4#usize) :
 NEB_PureFrame.run (Event:=Event) s (NEO_QRef.from_limbs x) =
 NEB_PureFrame.run s (FIo_Native.fast_pairing.canonical.Q.from_limbs x) := by
 rw [NEO_QRepresentation.from_limbs]

theorem wide_frame {S Event : Type} (s : S) (x : NE) :
 NEB_PureFrame.run (Event:=Event) s (NEO_QRef.from_wide (NEB_ArrayRefs.wordsE x)) =
 NEB_PureFrame.run s (FIo_Native.fast_pairing.canonical.Q.from_wide x) := by
 rw [NEO_QRepresentation.from_wide]

theorem public_frame {S Event : Type} (s : S) (x : NQ) :
 NEB_PureFrame.run (Event:=Event) s (NEO_QRef.limbs_of (NEB_ArrayRefs.wordsQ x)) =
 NEB_PureFrame.run s (FIo_Native.fast_pairing.limbs_of x) := by
 rw [NEO_QRepresentation.limbs_of]

/-- Same raw getter result feeds the actual constructor. Both rejected and
accepted outcomes remain, rather than postulating an accepted Q. -/
theorem checked_calls (x : NQ) :
 FIo_Native.fast_pairing.checked_q x =
 (do let words ← FIo_Native.fast_pairing.limbs_of x
     let parsed ← FIo_Native.fast_pairing.canonical.Q.from_limbs words
     match parsed with
     | none => ok (.Err ())
     | some q => ok (.Ok q)) := rfl

#print axioms carrier
#print axioms limbs_frame
#print axioms constructor_frame
#print axioms wide_frame
#print axioms public_frame
#print axioms checked_calls
end NEO_QComposition
