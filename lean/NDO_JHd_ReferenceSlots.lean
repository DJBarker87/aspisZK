import JHd_KeyStd
import NDO_JHd_RequestOperations
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHd_ReferenceSlots
open Aeneas Aeneas.Std Result
open _root_.AdapterRw

/-- Explicit reference-leaf selection. All remaining source children stay in
base; no authentication, scanner, reconstruction or emitter success is chosen. -/
def leaves (base : Ops) : Ops :=
  {base with
    op13:=ok 1#u8
    op14:=ok 2#u8
    op16:=ok 255#u8
    op18:=ok 1#u8
    op19:=ok 1520#usize
    op17:=JHd_RequestOperations.outputLane
    op20:=JHd_RequestOperations.nullifier
    op23:=JHd_RequestNative.decode}
def install (base : Ops) : Ops := JHd_KeyStd.install (leaves base)

theorem decode (base : Ops) : (install base).op23 JHb_DataRequest.value=
    ok (.Ok JHd_RequestCarrier.actual) := JHd_RequestNative.source
#print axioms decode

theorem nullifier (base : Ops) : (install base).op20 JHd_RequestCarrier.actual.«public»=
    ok JFt_Digest44.value := JHd_RequestOperations.nullifier_real
#print axioms nullifier

theorem lane (base : Ops) : (install base).op17 JFt_Digest44.value=ok (.Ok 3#u8) :=
  JHd_RequestOperations.lane_real
#print axioms lane
end AspisR1.JHd_ReferenceSlots
end
