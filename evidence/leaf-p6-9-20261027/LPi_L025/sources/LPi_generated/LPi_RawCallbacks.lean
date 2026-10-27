import FIo_QRawFuns
import JGi_QRawSourceForwardTotalityV1
set_option autoImplicit false
namespace AspisR1.LPi_RawCallbacks
open Aeneas Aeneas.Std Result

theorem left : FIo_QRaw.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 =
    AspisR1CanonicalQRawUnified.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64 := rfl

theorem right : FIo_QRaw.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 =
    AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64 := rfl

theorem partial (x : U64) :
    FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () x =
    AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () x := by
  simp only [FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call,
    AspisR1CanonicalQRawUnified.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call,
    FIo_QRaw.canonical.P,AspisR1CanonicalQRawUnified.canonical.P]

theorem pp : FIo_QRaw.canonical.Q.raw.PP = AspisR1CanonicalQRawUnified.canonical.Q.raw.PP := by
  simp only [FIo_QRaw.canonical.Q.raw.PP,AspisR1CanonicalQRawUnified.canonical.Q.raw.PP,
    FIo_QRaw.canonical.P,AspisR1CanonicalQRawUnified.canonical.P]

#print axioms left
#print axioms right
#print axioms partial
#print axioms pp
end AspisR1.LPi_RawCallbacks
