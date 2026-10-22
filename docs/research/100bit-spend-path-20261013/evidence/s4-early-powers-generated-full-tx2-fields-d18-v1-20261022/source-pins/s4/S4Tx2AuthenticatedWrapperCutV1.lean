import Stage2ContinuationQueryLoop
set_option autoImplicit false
open Aeneas Aeneas.Std Result ControlFlow
namespace AspisR1S4Tx2AuthenticatedWrapperCutV1
open AspisR1Stage2

abbrev Error := verifier.Error
abbrev Variant := transport.Variant
abbrev Accepted := core.result.Result Unit Error

/-- Literal source operation cut of the emitted `tx2_authenticated` wrapper.
The parse_shape, Parsed mark, and tx2_common bodies remain explicit source slots. -/
def tx2AuthenticatedOperationCut {H : Type}
    (inst : aspis_core.digest.Digest32 H)
    (parseShape : Slice U8 → Result (core.result.Result Variant Error))
    (mark : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit)
    (tx2Common : aspis_core.digest.Digest32 H → Slice U8 → Slice U8 → Slice U8 → H →
      Option (verifier.Phase → Result Unit) → Result Accepted)
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) : Result Accepted := do
  let r ← parseShape proof
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | Aeneas.Std.core.ops.control_flow.ControlFlow.Continue _ => do
    mark obs verifier.Phase.Parsed
    tx2Common inst public_bytes proof checkpoint hash obs
  | Aeneas.Std.core.ops.control_flow.ControlFlow.Break residual =>
    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
      Unit (core.convert.FromSame Error) residual

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β)
    (v : β) (h : (do let x ← m; k x) = .ok v) :
    ∃ x, m = .ok x ∧ k x = .ok v := by
  cases m with
  | ok x => exact ⟨x,rfl,h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem accepted_reaches_exact_common {H : Type}
    (inst : aspis_core.digest.Digest32 H)
    (parseShape : Slice U8 → Result (core.result.Result Variant Error))
    (mark : Option (verifier.Phase → Result Unit) → verifier.Phase → Result Unit)
    (tx2Common : aspis_core.digest.Digest32 H → Slice U8 → Slice U8 → Slice U8 → H →
      Option (verifier.Phase → Result Unit) → Result Accepted)
    (public_bytes proof checkpoint : Slice U8) (hash : H)
    (obs : Option (verifier.Phase → Result Unit))
    (h : tx2AuthenticatedOperationCut inst parseShape mark tx2Common
      public_bytes proof checkpoint hash obs = .ok (.Ok ())) :
    ∃ v : Variant,
      parseShape proof = .ok (.Ok v) ∧
      mark obs verifier.Phase.Parsed = .ok () ∧
      tx2Common inst public_bytes proof checkpoint hash obs = .ok (.Ok ()) := by
  unfold tx2AuthenticatedOperationCut at h
  obtain ⟨raw, hraw, hrest⟩ := bind_success _ _ _ h
  obtain ⟨cf, hcf, hmatch⟩ := bind_success _ _ _ hrest
  cases cf with
  | Continue v =>
    obtain ⟨u, hmark, hcommon⟩ := bind_success _ _ _ hmatch
    have hraw' : raw = core.result.Result.Ok v := by
      cases raw with
      | Ok inner =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch] at hcf
        injection hcf with hv
        cases hv
        rfl
      | Err e => simp [core.result.Result.Insts.CoreOpsTry.branch] at hcf
    exact ⟨v, by rw [hraw, hraw'], hmark, hcommon⟩
  | Break residual =>
    cases residual with
    | Ok impossible => exact nomatch impossible
    | Err e => simp [core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual] at hmatch

#print axioms accepted_reaches_exact_common
end AspisR1S4Tx2AuthenticatedWrapperCutV1
