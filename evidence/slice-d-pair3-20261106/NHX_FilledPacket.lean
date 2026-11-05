import NHM_Filled64
set_option autoImplicit false
namespace NHX_FilledPacket
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues NP6_StdModel

/-- The arbitrary native prestate is not a repeated-value xs. This is its
exact selected-cell interpretation, including all cells preserved by resize. -/
def window {T : Type} (xs : List T) (value : T) : List T := xs ++ [value]

theorem initialized {T : Type} (xs : List T) (value : T) :
 (window xs value)[xs.length]?=some value := by
 simpa [window] using NHM_FilledFrame.window xs value xs.length

theorem frame {T : Type} (xs : List T) (value : T) (i : Nat)
 (inside : i<xs.length) : (window xs value)[i]?=xs[i]? := by
 exact List.getElem?_append_left inside

/-- Native resize windows compose on the SAME vector from the successful
reserve arm. The error arm is retained by the inherited full-Result law. -/
theorem source (reservation : Reservation) (value : NQ) :
 letI := FIo_Install.allocation reservation
 FIo_FieldBridge.map NHM_Filled64.reply
  (FIo_Native.aspis_core.r0.heap.filled FIo_Native.aspis_core.field.QM31.Insts.CoreMarkerCopy
    64#usize value)=NHI_FilledRef.filled_ref 64#usize (NHI_WordEncoding.words value) := by
 exact NHM_Filled64.cohort reservation value

#print axioms initialized
#print axioms frame
#print axioms source
end NHX_FilledPacket
