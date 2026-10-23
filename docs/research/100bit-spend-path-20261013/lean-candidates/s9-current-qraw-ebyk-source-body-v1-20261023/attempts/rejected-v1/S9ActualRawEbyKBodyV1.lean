import S9ActualRawNativeHookV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualRawEbyKBodyV1
open AspisR1S9ActualEbyKBackendTransportV1
open AspisR1S9ActualRawNativeOperandsV1
open AspisR1S9ActualRawNativeHookV1
abbrev R4 := Array U64 4#usize
def dotWithRaw (raw : A4 → A4 → Result R4)
  (self : fast_pairing.canonical.Dot) (a : fast_pairing.canonical.Q)
  (b : fast_pairing.canonical.Q) :
  Result fast_pairing.canonical.Dot
  := do
  let raw1 ← raw a b
  fast_pairing.canonical.Dot.push_loop { start := 0#usize, «end» := 4#usize }
    self raw1

def pushWithRaw (raw : A4 → A4 → Result R4)
  (self : fast_pairing.EbyKDot) (value : aspis_core.field.wide_exact.WideExact)
  (scalar : aspis_core.field.QM31) :
  Result ((core.result.Result Unit Unit) × fast_pairing.EbyKDot)
  := do
  if self.count >= fast_pairing.MAX_TERMS
  then ok (core.result.Result.Err (), self)
  else
    let a ← fast_pairing.canonical.Q.from_wide value
    let value_c0 ← Array.index_usize a 0#usize
    let value_c1 ← Array.index_usize a 1#usize
    let r ← fast_pairing.checked_q scalar
    let cf ← core.result.Result.Insts.CoreOpsTry.branch r
    match cf with
    | core.ops.control_flow.ControlFlow.Continue val =>
      let d ← dotWithRaw raw self.c0 value_c0 val
      let d1 ← dotWithRaw raw self.c1 value_c1 val
      let i ← lift (Std.Usize.wrapping_add self.count 1#usize)
      ok (core.result.Result.Ok (), { c0 := d, c1 := d1, count := i })
    | core.ops.control_flow.ControlFlow.Break residual =>
      let r1 ←
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame Unit) residual
      ok (r1, self)


/-- Exact extracted source body, factored over its raw callee. -/
theorem model_dot_factor (self : fast_pairing.canonical.Dot) (a b : A4) :
    fast_pairing.canonical.Dot.push self a b =
      dotWithRaw AspisR1S9ActualDotBackendMapV1.actualRaw self a b := by rfl

theorem model_ebyk_factor (self : fast_pairing.EbyKDot) (w : NativeW) (scalar : NativeQ) :
    fast_pairing.EbyKDot.push self w scalar =
      pushWithRaw AspisR1S9ActualDotBackendMapV1.actualRaw self w scalar := by rfl

/-- Full Result transport for the exact source-body raw-callee substitution.
All counts and scalar values are covered, including count and scalar rejection;
only the current Wide input limb bounds are retained. -/
theorem actual_raw_source_body_eq_model (self : fast_pairing.EbyKDot)
    (w : NativeW) (scalar : NativeQ)
    (hw : w.c0.c0.a.val ≤ 2^31-2 ∧ w.c0.c0.b.val ≤ 2^31-2 ∧
      w.c0.c1.a.val ≤ 2^31-2 ∧ w.c0.c1.b.val ≤ 2^31-2 ∧
      w.c1.c0.a.val ≤ 2^31-2 ∧ w.c1.c0.b.val ≤ 2^31-2 ∧
      w.c1.c1.a.val ≤ 2^31-2 ∧ w.c1.c1.b.val ≤ 2^31-2)
    : pushWithRaw AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw self w scalar =
        fast_pairing.EbyKDot.push self w scalar := by
  rw [model_ebyk_factor]
  unfold pushWithRaw
  split
  · rfl
  · simp only [actual_from_wide_same_lanes,bind_tc_ok]
    change (do
      let r ← fast_pairing.checked_q scalar
      let cf ← core.result.Result.Insts.CoreOpsTry.branch r
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val => do
        let d ← dotWithRaw AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw self.c0 (low w) val
        let d1 ← dotWithRaw AspisR1S9ActualRawCutV1.fast_pairing.canonical.Q.raw self.c1 (high w) val
        let i ← lift (Usize.wrapping_add self.count 1#usize)
        ok (.Ok (),{c0:=d,c1:=d1,count:=i})
      | core.ops.control_flow.ControlFlow.Break residual => do
        let r1 ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
          Unit (core.convert.FromSame Unit) residual
        ok (r1,self)) = _
    cases hc : fast_pairing.checked_q scalar with
    | fail err => simp only [hc,bind_tc_fail]
    | div => simp only [hc,bind_tc_div]
    | ok r =>
      cases r with
      | Err e => simp only [hc,bind_tc_ok]; rfl
      | Ok q =>
        obtain ⟨hlo,hhi⟩ := actual_same_operands_raw_hook w scalar q hw hc
        simp only [hc,bind_tc_ok]
        unfold core.result.Result.Insts.CoreOpsTry.branch
        simp only [bind_tc_ok]
        unfold dotWithRaw
        rw [hlo,hhi]

#print axioms model_dot_factor
#print axioms model_ebyk_factor
#print axioms actual_raw_source_body_eq_model
end AspisR1S9ActualRawEbyKBodyV1
