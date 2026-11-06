import NKI_InitialPrefix
import NLH_CompositionState
set_option autoImplicit false
noncomputable section
namespace AspisR1.NLH_CompRun
open Aeneas Aeneas.Std Result FIq_Native NLH_CompositionState
open FIv_NativeArithmetic (NQ)
open NKI_InitialPrefix (Public)
def zeros (n : Usize) : Array NQ n := Array.repeat n field.QM31.ZERO
def initial : State :=
 {openings := ⟨zeros 16#usize,zeros 16#usize,zeros 16#usize⟩,  mask := zeros 10#usize,selectors := ⟨zeros 64#usize,zeros 16#usize⟩,  poseidonSelectors := ⟨field.QM31.ZERO,zeros 16#usize⟩,  poseidon := zeros 4#usize,semantic := zeros 24#usize,h := field.QM31.ZERO,  copyVariant := .PrivateTransfer,copy := ⟨field.QM31.ZERO,field.QM31.ZERO⟩,  prepared := NJB_PreparedCarrier.value (fun _ _ => 0#u32),composition := field.QM31.ZERO,  remaining := [],g := field.QM31.ZERO}
def project : core.result.Result State NLH_CompositionState.Error → core.result.Result NKR_TermTail.Carrier NLH_CompositionState.Error
 | .Err e => .Err e
 | .Ok st => .Ok (returned st)
def reference (pub : Public) (claims : Array NQ 84#usize) (point : Array NQ 10#usize) (lambda chi theta : NQ) := do
 let r ← NLH_FoldRust.run (step pub claims point lambda chi theta) order initial
 ok (project r)
end AspisR1.NLH_CompRun
end
