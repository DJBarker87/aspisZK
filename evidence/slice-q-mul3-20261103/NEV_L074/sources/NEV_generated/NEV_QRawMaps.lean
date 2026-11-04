import NEV_QRaw.Funs
import LPi_RawAssociation
import LPf_ArrayFour
set_option autoImplicit false
noncomputable section
namespace NEV_QRawMaps
open Aeneas Aeneas.Std Result AspisR1
abbrev W (x : U32) : U64 := core.convert.num.FromU64U32.from x
/-- Finite four-entry carrier map only; multiplication is never reduced. -/
theorem left (a b c d : U32) :
    core.array.Array.map FIo_QRaw.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnMutTupleU32U64
      (Array.make 4#usize [a,b,c,d]) ()=ok (Array.make 4#usize [W a,W b,W c,W d]) := by rfl

theorem right (a b c d : U32) :
    core.array.Array.map FIo_QRaw.canonical.Q.raw.closure_1.Insts.CoreOpsFunctionFnMutTupleU32U64
      (Array.make 4#usize [a,b,c,d]) ()=ok (Array.make 4#usize [W a,W b,W c,W d]) := by rfl

theorem shift (x : U64) : (x >>> 31#u32)=(x >>> 31#i32) := by rfl

theorem fold (x : U64) :
    NEV_QRaw.fast_pairing.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnTupleU64U64.call () x =
      FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call () x := by
  simp only [NEV_QRaw.fast_pairing.canonical.Q.raw.closure.Insts.CoreOpsFunctionFnTupleU64U64.call,
    FIo_QRaw.canonical.Q.raw.closure_2.Insts.CoreOpsFunctionFnTupleU64U64.call,
    NEV_QRaw.fast_pairing.canonical.P,FIo_QRaw.canonical.P,shift]
#print axioms left
#print axioms right
#print axioms shift
#print axioms fold
end NEV_QRawMaps
end
