import R1Z.PV_DL_Wrap
import R1Z.PV_DL_DefaultBuffer
open Aeneas Aeneas.Std Result
namespace R1Z.PV_DL_WrapLaw
open PV_CBL_LibraryShapes PV_CBL_GenericArrayPower
set_option autoImplicit false

def observe {T : Type} (v : Wrapper T (Storage U8 6)) : T × List U8 × Nat :=
  (v.core,flatten 6 v.buffer.buffer,v.buffer.pos.val)

def observeReference {T : Type} (v : T × Array U8 64#usize × Usize) : T × List U8 × Nat :=
  (v.1,v.2.1.val,v.2.2.val)

/-- Full value correspondence at the owned moved-core boundary. No equality
between a native callback and its selected replacement is assumed here. -/
theorem source_reference {T : Type} (core : T) :
    (do let v ← PV_DL_DefaultBuffer.model (ok core);ok (observe v)) =
    (do let v ← PV_DL_Wrap.wrap_reference core;ok (observeReference v)) := by
  rw [PV_DL_DefaultBuffer.success]
  simp only [bind_tc_ok,observe,PV_DL_DefaultBuffer.initial,PV_DL_DefaultBuffer.bytes,
    PV_DL_Wrap.wrap_reference,observeReference,Array.repeat]
  rfl

#print axioms observe
#print axioms observeReference
#print axioms source_reference
end R1Z.PV_DL_WrapLaw
