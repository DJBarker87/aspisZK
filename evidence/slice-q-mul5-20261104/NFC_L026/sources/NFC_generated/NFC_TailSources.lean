import NFC_TailState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFC_TailSources
open Aeneas Aeneas.Std Result NEV_DotCarrier

def first (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize) : Result (NE×NQ) := do
  let value ← Array.index_usize g 28#usize
  let base ← slot*120#usize
  let start ← base+104#usize
  let stop ← base+120#usize
  let scalar ← NFA_TailQM.read q start stop
  ok (value,scalar)

def later (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients)
    (base position : Usize) : Result (NE×NQ) := do
  let origin ← 480#usize+base
  let offset ← position*16#usize
  let start ← origin+offset
  let index ← position+26#usize
  let value ← Array.index_usize g index
  let stop ← start+16#usize
  let scalar ← NFA_TailQM.read q start stop
  ok (value,scalar)

def push (state : NFC_TailTrace.Acc) (operands : NE×NQ) : Result NFC_TailTrace.Acc := do
  let (result,after) ← FIo_Native.fast_pairing.EbyKDot.push state operands.1 operands.2
  core.result.Result.unwrap core.fmt.DebugUnit result
  ok after

def body (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize) : Result NE := do
  let state ← FIo_Native.fast_pairing.EbyKDot.new
  let args ← first q g slot
  let state ← push state args
  let base ← slot*32#usize
  let args ← later q g base 0#usize
  let state ← push state args
  let args ← later q g base 1#usize
  let state ← push state args
  FIo_Native.fast_pairing.EbyKDot.finish state

/-- Complete Result factorization preserves the read/push interleaving and
all rejection and divergence paths. No reordering of later reads is used. -/
theorem association (q : Array U8 608#usize) (g : NEV_DotInputs.Coefficients) (slot : Usize) :
    NFA_SuffixFactor.tail q g slot=body q g slot := by
  simp only [NFA_SuffixFactor.tail,body,first,later,push,NFA_TailQM.read,
    Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok]
  repeat' first
  | rfl
  | (apply (Aeneas.Std.bind_eq_iff _ _ _).mpr
     intro x hx
     cases x
     simp only [Aeneas.Std.uncurry,bind_assoc_eq,bind_tc_ok])

#print axioms association
end AspisR1.NFC_TailSources
end
