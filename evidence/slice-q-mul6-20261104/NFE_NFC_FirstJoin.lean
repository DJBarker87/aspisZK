import NFE_NFC_TailSources
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFC_FirstJoin
open Aeneas Aeneas.Std Result NEV_DotCarrier NFE_NFC_TailSources
/-- Only the first read/push cut is normalized, with arbitrary continuation. -/
theorem association {T : Type} (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (slot : Usize) (state : NFE_NFC_TailTrace.Acc) (next : NFE_NFC_TailTrace.Acc → Result T) :
    (do let args ← first q g slot; let after ← push state args; next after) =
    (do let value ← Array.index_usize g 28#usize
        let base ← slot*120#usize
        let start ← base+104#usize
        let stop ← base+120#usize
        let scalar ← NFA_TailQM.read q start stop
        let (result,after) ← FIo_Native.fast_pairing.EbyKDot.push state value scalar
        core.result.Result.unwrap core.fmt.DebugUnit result
        next after) := by
  simp only [first,push,bind_assoc_eq,bind_tc_ok]
  repeat' first
  | rfl
  | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
     intro x hx
     cases x
     simp only [Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok])
#print axioms association
end AspisR1.NFE_NFC_FirstJoin
end
