import ExtractedTx1Model

/-! Success inversion of the complete emitted approved tx1 body. Actual
observer dispatch, allocation constructor and error closures are retained;
View.parse, verify_observed, heap allocation, powers and query/checkpoint tail
remain explicit function parameters. No helper reachability inside verify,
full25 hread, downstream arithmetic, SDK or custody theorem is asserted. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.Tx1Reachability

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

/-- Exact initialized result follows from actual constructor success, without
assuming allocation success or accepting any staging panic definition. -/
theorem accumulator_success (B : Tx1Model.Boundaries) (v : transport.Variant)
    (out : verifier.Accumulator)
    (h : Tx1Model.newAccumulator B v = ok (.Ok out)) :
    ∃ n weights,
      Tx1Model.final_len v = ok n ∧
      B.filled Tx1Model.copyInst n aspis_core.field.QM31.ZERO = ok (.Ok weights) ∧
      out = ⟨weights, aspis_core.field.WideExact.ZERO, Tx1Model.one, 0#usize⟩ := by
  unfold Tx1Model.newAccumulator at h
  obtain ⟨n, hn, h⟩ := bind_success _ _ _ h
  obtain ⟨r, hr, h⟩ := bind_success _ _ _ h
  cases r with
  | Err e =>
    simp only [core.result.Result.map_err, Tx1Model.allocationErrorClosure,
      Tx1Model.allocationError, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    cases h
  | Ok weights =>
    simp only [core.result.Result.map_err, bind_tc_ok,
      core.result.Result.Insts.CoreOpsTry.branch] at h
    exact ⟨n, weights, hn, hr, (core.result.Result.Ok.inj (Result.ok.inj h)).symm⟩

/-- All prefix calls and the final tail are reached on actual tx1 acceptance.
No supplied child-call success, chosen View/semantic/prepared value or observer
success is a premise. The same supplied pub and exact returned View.semantic
bytes reach the named verify boundary. -/
theorem tx1_success (B : Tx1Model.Boundaries) (P : PreparedModel.Boundaries)
    {H : Type} (D : aspis_core.Digest32 H)
    (pub : pool_v1.pair_forest_semantic_terminal.r0.Public)
    (publicBytes proof : Slice U8) (k : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (out : alloc.vec.Vec U8)
    (h : Tx1Model.tx1 B P D pub publicBytes proof k hash obs = ok (.Ok out)) :
    k.val ≤ 22 ∧ ∃ v sem prepared acc g,
      B.view proof = ok (.Ok v) ∧
      Tx1Model.mark obs .Parsed = ok () ∧
      B.verify D pub v.semantic hash obs = ok (.Ok sem) ∧
      Tx1Model.mark obs .Semantic = ok () ∧
      PreparedModel.prepare P D sem v hash = ok (.Ok prepared) ∧
      Tx1Model.newAccumulator B v.variant = ok (.Ok acc) ∧
      B.powers 29#usize prepared.gamma = ok g ∧
      Tx1Model.mark obs .Prepare = ok () ∧
      B.finish D v prepared acc g publicBytes proof k hash obs = ok (.Ok out) := by
  unfold Tx1Model.tx1 at h
  split at h
  · cases h
  · rename_i hk
    have hbound : k.val ≤ 22 := by scalar_tac
    obtain ⟨viewResult, hv, h⟩ := bind_success _ _ _ h
    cases viewResult with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok] at h
      cases h
    | Ok v =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      obtain ⟨u, hp, h⟩ := bind_success _ _ _ h
      cases u
      obtain ⟨semResult, hs, h⟩ := bind_success _ _ _ h
      cases semResult with
      | Err e =>
        simp only [core.result.Result.map_err, Tx1Model.semanticErrorClosure,
          Tx1Model.semanticError, bind_tc_ok, core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from] at h
        cases h
      | Ok sem =>
        simp only [core.result.Result.map_err, core.result.Result.Insts.CoreOpsTry.branch,
          bind_tc_ok] at h
        obtain ⟨u, hsm, h⟩ := bind_success _ _ _ h
        cases u
        obtain ⟨prepResult, hprep, h⟩ := bind_success _ _ _ h
        cases prepResult with
        | Err e =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from, bind_tc_ok] at h
          cases h
        | Ok prepared =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
          obtain ⟨accResult, ha, h⟩ := bind_success _ _ _ h
          cases accResult with
          | Err e =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from, bind_tc_ok] at h
            cases h
          | Ok acc =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
            obtain ⟨g, hg, h⟩ := bind_success _ _ _ h
            obtain ⟨u, hm, hf⟩ := bind_success _ _ _ h
            cases u
            exact ⟨hbound, v, sem, prepared, acc, g, hv, hp, hs, hsm,
              hprep, ha, hg, hm, hf⟩

#print axioms accumulator_success
#print axioms tx1_success
end AspisR1PublicPreparation.Tx1Reachability
