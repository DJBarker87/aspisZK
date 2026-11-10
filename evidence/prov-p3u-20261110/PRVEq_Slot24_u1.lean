import NNH_S1HostCodec
import PRVEq_AspisR1TerminalDecoder_Funs_j1
set_option autoImplicit false
noncomputable section
namespace PCVX_Slot24
open Aeneas Aeneas.Std Result

/-- The frozen emission (PCQG pair_terminal_b, 4bb3b3f, overflow ON) of
`encode_pool_v1_pair_verified_afterstate_v1`, in the namespace of PRVEq_..._Funs_j1. -/
abbrev F := @AspisR1TerminalDecoder.PRVFresh_AspisR1TerminalDecoder_Funs_j1.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1

theorem fresh_eq_gate : F = @AspisR1TerminalDecoder.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1 :=
 PRVEq.AspisR1TerminalDecoder.Funs_j1.pool_v1.pair_terminal.encode_pool_v1_pair_verified_afterstate_v1

/-- The deployed op24 (NNH_S1HostCodec.encode) is the weak-Err mapping of the frozen emission applied to the
carrier of the afterstate. Every afterstate; the only deviation from the emission is that a returned Err becomes
`div` (model-fidelity note, lead ruling K6). -/
theorem slot24 (a : AspisR1.NNH_S1HostCodec.Afterstate) :
 AspisR1.NNH_S1HostCodec.encode a =
 (match NMT_345.mapOuter (NMT_345.mapCore id NMT_345Dec.fromT11) (F (NMT_345Dec.toT5 (AspisR1.NNH_S1HostCodec.afterCarrier a))) with
  | .ok (.Ok out) => .ok (.Ok out)
  | .ok (.Err _) => .div
  | .fail e => .fail e
  | .div => .div) := by
 unfold AspisR1.NNH_S1HostCodec.encode NMT_345.encodeCall
 rw [fresh_eq_gate]
 rfl

theorem slot24_ok (a : AspisR1.NNH_S1HostCodec.Afterstate) (out)
 (h : F (NMT_345Dec.toT5 (AspisR1.NNH_S1HostCodec.afterCarrier a)) = .ok (.Ok out)) :
 AspisR1.NNH_S1HostCodec.encode a = .ok (.Ok out) := by
 rw [slot24, h]; rfl

theorem slot24_err (a : AspisR1.NNH_S1HostCodec.Afterstate) (e)
 (h : F (NMT_345Dec.toT5 (AspisR1.NNH_S1HostCodec.afterCarrier a)) = .ok (.Err e)) :
 AspisR1.NNH_S1HostCodec.encode a = .div := by
 rw [slot24, h]; rfl

#print axioms fresh_eq_gate
#print axioms slot24
#print axioms slot24_ok
#print axioms slot24_err
end PCVX_Slot24
end
