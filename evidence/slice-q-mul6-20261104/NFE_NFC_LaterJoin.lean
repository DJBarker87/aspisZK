import NFE_NFC_TailSources
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFE_NFC_LaterJoin
open Aeneas Aeneas.Std Result NEV_DotCarrier NFE_NFC_TailSources
/-- One later read/push cut, keeping its literal checked arithmetic order. -/
theorem association {T : Type} (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (base position : Usize) (state : NFE_NFC_TailTrace.Acc) (next : NFE_NFC_TailTrace.Acc → Result T) :
    (do let args ← later q g base position; let after ← push state args; next after) =
    (do let origin ← 480#usize+base
        let offset ← position*16#usize
        let start ← origin+offset
        let index ← position+26#usize
        let value ← Array.index_usize g index
        let stop ← start+16#usize
        let scalar ← NFA_TailQM.read q start stop
        let (result,after) ← FIo_Native.fast_pairing.EbyKDot.push state value scalar
        core.result.Result.unwrap core.fmt.DebugUnit result
        next after) := by
  simp only [later,push,bind_assoc_eq,bind_tc_ok]
  repeat' first
  | rfl
  | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
     intro x hx
     cases x
     simp only [Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok])
#print axioms association
end AspisR1.NFE_NFC_LaterJoin
end
