import NNH_S1HostCodec
import PRVEq_AspisR1TerminalDecoder_Funs_u1
set_option autoImplicit false
noncomputable section
namespace PCVX_Slot21
open Aeneas Aeneas.Std Result AspisR1 AdapterRw NND_Carrier NNH_Libraries

/-- The frozen emission (PCVX_E006, 4bb3b3f, overflow ON, original Aeneas 959659a6) of
`validate_pool_v1_pair_forest_terminal_statement_v1`. -/
abbrev F := @AspisR1TerminalDecoder.PRVFresh_AspisR1TerminalDecoder_Funs_u1.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1

theorem fresh_eq_gate : F = @AspisR1TerminalDecoder.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1 :=
 PRVEq.AspisR1TerminalDecoder.Funs_u1.pool_v1.pair_forest_terminal.validate_pool_v1_pair_forest_terminal_statement_v1

/-- Deployed op21 (NNH_S1HostCodec.validate) is the weak-Err mapping of the frozen emission applied to the
carrier of the statement. Every statement; a returned Err becomes `div` (model-fidelity note, lead ruling K6). -/
theorem slot21 (st : AspisR1.NNH_S1HostCodec.Statement) :
 AspisR1.NNH_S1HostCodec.validate st =
 (match NMT_345.mapOuter (NMT_345.mapCore id NMT_345Dec.fromT13) (F (NMT_345Dec.toT8 (NNH_S1DecodeOk.carrier st))) with
  | .ok (.Ok u) => .ok (.Ok u)
  | .ok (.Err _) => .div
  | .fail e => .fail e
  | .div => .div) := by
 unfold AspisR1.NNH_S1HostCodec.validate NMT_345.validateCall
 rw [fresh_eq_gate]
 rfl

theorem slot21_ok (st : AspisR1.NNH_S1HostCodec.Statement) (u)
 (h : F (NMT_345Dec.toT8 (NNH_S1DecodeOk.carrier st)) = .ok (.Ok u)) :
 AspisR1.NNH_S1HostCodec.validate st = .ok (.Ok u) := by
 rw [slot21, h]; rfl

theorem slot21_err (st : AspisR1.NNH_S1HostCodec.Statement) (e)
 (h : F (NMT_345Dec.toT8 (NNH_S1DecodeOk.carrier st)) = .ok (.Err e)) :
 AspisR1.NNH_S1HostCodec.validate st = .div := by
 rw [slot21, h]; rfl

/-- On the decoded-statement domain of NNH_S1DecodeOk: a successful S1 decode of the public data yields a native
statement whose deployed validate is the weak-Err map of the frozen emission at the carried statement. -/
theorem slot21_on_decoded (publicData : Slice U8) (st : C.Statement)
 (success : C.decodeStatement (LIB_Carriers.bytes publicData) = some st) :
 ∃ native, AspisS6CurrentCodecInstallation.decode publicData = .ok (.Ok native) ∧
  NNH_S1DecodeOk.carrier native = st ∧
  AspisR1.NNH_S1HostCodec.validate native =
  (match NMT_345.mapOuter (NMT_345.mapCore id NMT_345Dec.fromT13) (F (NMT_345Dec.toT8 st)) with
   | .ok (.Ok u) => .ok (.Ok u)
   | .ok (.Err _) => .div
   | .fail e => .fail e
   | .div => .div) := by
 obtain ⟨native, hd, hc⟩ := NNH_S1DecodeOk.source publicData st success
 refine ⟨native, hd, hc, ?_⟩
 rw [slot21, hc]

#print axioms fresh_eq_gate
#print axioms slot21
#print axioms slot21_ok
#print axioms slot21_err
#print axioms slot21_on_decoded
end PCVX_Slot21
end
