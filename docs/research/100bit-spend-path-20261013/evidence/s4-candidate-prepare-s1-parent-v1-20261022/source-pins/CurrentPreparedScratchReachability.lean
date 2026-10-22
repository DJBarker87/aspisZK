import CurrentPreparedScratchModel

/-! Reachability of the exact approved Prepared body, retaining its explicit
arithmetic/query boundaries. Success premises for child calls are conclusions. -/
set_option autoImplicit false
open Aeneas Aeneas.Std Result
namespace AspisR1PublicPreparation.PreparedScratchReachability
open PreparedModel
abbrev Wide := aspis_core.field.WideExact
abbrev QM := aspis_core.field.QM31
abbrev Bytes32 := Array U8 32#usize

private theorem bind_success {α β : Type} (m : Result α) (k : α → Result β) (v : β)
    (h : (do let x ← m; k x) = ok v) :
    ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem pair_bind_success {α β γ : Type} (m : Result (α × β))
    (k : α → β → Result γ) (v : γ)
    (h : (do let (a, b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a, b) ∧ k a b = ok v := by
  cases m with
  | ok pair => cases pair with | mk a b => exact ⟨a, b, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

def emptyPayload : Slice U8 := Array.to_slice (Std.Array.empty U8)

def output {H : Type} (sem : r1_semantic.Verified H) (v : verifier.View)
    (gamma kappa : Wide) (alpha : Array Wide 2#usize) (rho : QM)
    (queries : Array U32 22#usize) (claim : Wide) (last : transcript.Transcript H) : verifier.Prepared :=
  { variant := v.variant, roots := sem.roots, gamma, kappa, alpha, rho, queries,
    semantic_alpha := sem.alpha, z := sem.z, claim, state := last.state }

def AfterQueries {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (gamma kappa : Wide)
    (alpha : Array Wide 2#usize) (row : U8) (before : transcript.Transcript H)
    (out : verifier.Prepared) (scratch : Array Wide 29#usize) : Prop :=
  ∃ (queries : Array U32 22#usize) (afterQueries last : transcript.Transcript H)
    (rho : QM) (claim : Wide),
    B.sampling.queries D before row v.final_message = ok (.Ok queries, afterQueries) ∧
    PreparedModel.scalar_k B.sampling D afterQueries (if row = 30#u8 then 31#u8 else 32#u8)
      emptyPayload = ok (rho, last) ∧
    B.powers 29#usize gamma = ok scratch ∧
    B.claim D sem v.y1 v.inactive scratch kappa = ok (.Ok claim) ∧
    out = output sem v gamma kappa alpha rho queries claim last

inductive Tail {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (gamma kappa alpha0 : Wide)
    (before : transcript.Transcript H) (out : verifier.Prepared) (scratch : Array Wide 29#usize) : Prop
  | single (hfolds : transport.Variant.folds v.variant = ok 1#usize)
      (tail : AfterQueries B D sem v gamma kappa
        (Array.make 2#usize [alpha0, aspis_core.field.WideExact.ZERO]) 30#u8 before out scratch) :
      Tail B D sem v gamma kappa alpha0 before out scratch
  | double (hfolds : transport.Variant.folds v.variant = ok 2#usize)
      (root : Bytes32) (bytes1 bytes2 : alloc.vec.Vec U8) (alpha1 : Wide)
      (afterAlpha : transcript.Transcript H)
      (hroot : core.option.Option.unwrap v.folded_root = ok root)
      (hbytes1 : alloc.vec.Vec.extend_from_slice core.clone.CloneU8
        (alloc.vec.Vec.with_capacity U8 256#usize) (Array.to_slice root) = ok bytes1)
      (hbytes2 : alloc.vec.Vec.extend_from_slice core.clone.CloneU8 bytes1 v.round1 = ok bytes2)
      (halpha1 : PreparedModel.scalar B.sampling D before 30#u8 (alloc.vec.Vec.deref bytes2) false =
        ok (alpha1, afterAlpha))
      (tail : AfterQueries B D sem v gamma kappa (Array.make 2#usize [alpha0, alpha1])
        31#u8 afterAlpha out scratch) : Tail B D sem v gamma kappa alpha0 before out scratch

def Reachable {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (out : verifier.Prepared) (scratch : Array Wide 29#usize) : Prop :=
  ∃ (start t1 t2 t3 : transcript.Transcript H) (inactiveBytes : Bytes32)
    (gamma kappa alpha0 : Wide),
    transcript.Transcript.new D hash sem.transcript.state v.variant = ok start ∧
    PreparedModel.scalar B.sampling D start 27#u8 v.y1 true = ok (gamma, t1) ∧
    B.sampling.toBytes v.inactive = ok inactiveBytes ∧
    PreparedModel.scalar B.sampling D t1 28#u8 (Array.to_slice inactiveBytes) false = ok (kappa, t2) ∧
    PreparedModel.scalar B.sampling D t2 29#u8 v.round0 false = ok (alpha0, t3) ∧
    Tail B D sem v gamma kappa alpha0 t3 out scratch

/-- All six source rows on the two-fold path (five on S1), with their exact
returned-state links. Queries retains the state returned by its explicit boundary. -/
theorem prepare_success {H : Type} (B : PreparedScratchModel.Boundaries) (D : aspis_core.Digest32 H)
    (sem : r1_semantic.Verified H) (v : verifier.View) (hash : H) (out : verifier.Prepared) (scratch : Array Wide 29#usize)
    (scratchIn : Array Wide 29#usize)
    (h : PreparedScratchModel.prepare B D sem v hash scratchIn = ok (.Ok out, scratch)) :
    Reachable B D sem v hash out scratch := by
  have add_exact {ty : UScalarTy} (a b c : UScalar ty)
      (hc : c.val = a.val + b.val) : a + b = ok c := by
    obtain ⟨z, hz, hval⟩ := WP.spec_imp_exists
      (UScalar.add_spec (x := a) (y := b) (by scalar_tac))
    have he : z = c := by scalar_tac
    simpa only [he] using hz
  have hcap : 32#usize + 224#usize = ok 256#usize := add_exact _ _ _ (by scalar_tac)
  have hsingle : 30#u8 + 1#u8 = ok 31#u8 := add_exact _ _ _ (by scalar_tac)
  have hdouble : 31#u8 + 1#u8 = ok 32#u8 := add_exact _ _ _ (by scalar_tac)
  unfold PreparedScratchModel.prepare at h
  simp only [r1_wire.SemanticTranscript.impl.state, bind_tc_ok] at h
  obtain ⟨start, hseed, h⟩ := bind_success _ _ _ h
  obtain ⟨gamma, t1, hgamma, h⟩ := pair_bind_success _ _ _ h
  obtain ⟨inactiveBytes, hbytes, h⟩ := bind_success _ _ _ h
  simp only [lift, bind_tc_ok] at h
  obtain ⟨kappa, t2, hkappa, h⟩ := pair_bind_success _ _ _ h
  obtain ⟨alpha0, t3, halpha0, h⟩ := pair_bind_success _ _ _ h
  obtain ⟨folds, hfolds, h⟩ := bind_success _ _ _ h
  refine ⟨start, t1, t2, t3, inactiveBytes, gamma, kappa, alpha0, hseed, hgamma,
    hbytes, hkappa, halpha0, ?_⟩
  split at h
  · rename_i htwo
    subst folds
    simp only [hcap, lift, bind_tc_ok] at h
    obtain ⟨root, hroot, h⟩ := bind_success _ _ _ h
    try simp only [lift, bind_tc_ok] at h
    obtain ⟨bytes1, hbytes1, h⟩ := bind_success _ _ _ h
    obtain ⟨bytes2, hbytes2, h⟩ := bind_success _ _ _ h
    obtain ⟨alpha1, afterAlpha, halpha1, h⟩ := pair_bind_success _ _ _ h
    obtain ⟨ret, afterQueries, hqueries, h⟩ := pair_bind_success _ _ _ h
    have hok : ∃ queries, ret = core.result.Result.Ok queries := by
      cases ret with
      | Ok queries => exact ⟨queries, rfl⟩
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, bind_tc_ok] at h
        cases h
    obtain ⟨queries, rfl⟩ := hok
    simp only [core.result.Result.Insts.CoreOpsTry.branch, hsingle, hdouble, lift, bind_tc_ok] at h
    obtain ⟨rho, last, hrho, h⟩ := pair_bind_success _ _ _ h
    obtain ⟨computed, hpowers, h⟩ := bind_success _ _ _ h
    obtain ⟨ret, hclaim, h⟩ := bind_success _ _ _ h
    cases ret with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok] at h
      cases h
    | Ok claim =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      apply Tail.double hfolds root bytes1 bytes2 alpha1 afterAlpha hroot hbytes1 hbytes2 halpha1
      have hp := Result.ok.inj h
      have hs : computed = scratch := congrArg Prod.snd hp
      subst computed
      refine ⟨queries, afterQueries, last, rho, claim, hqueries, ?_, hpowers, hclaim, ?_⟩
      · simpa [emptyPayload] using hrho
      · exact (core.result.Result.Ok.inj (congrArg Prod.fst hp)).symm
  · rename_i htwo
    have hone : folds = 1#usize := by
      cases hv : v.variant <;>
        simp [transport.Variant.folds, transport.Variant.Insts.CoreCmpPartialEqVariant.eq, read_discriminant, transport.Variant.read_discriminant, hv] at hfolds <;>
        subst folds <;> first | rfl | contradiction
    subst folds
    obtain ⟨ret, afterQueries, hqueries, h⟩ := pair_bind_success _ _ _ h
    have hok : ∃ queries, ret = core.result.Result.Ok queries := by
      cases ret with
      | Ok queries => exact ⟨queries, rfl⟩
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from, bind_tc_ok] at h
        cases h
    obtain ⟨queries, rfl⟩ := hok
    simp only [core.result.Result.Insts.CoreOpsTry.branch, hsingle, hdouble, lift, bind_tc_ok] at h
    obtain ⟨rho, last, hrho, h⟩ := pair_bind_success _ _ _ h
    obtain ⟨computed, hpowers, h⟩ := bind_success _ _ _ h
    obtain ⟨ret, hclaim, h⟩ := bind_success _ _ _ h
    cases ret with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from, bind_tc_ok] at h
      cases h
    | Ok claim =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_tc_ok] at h
      apply Tail.single hfolds
      have hp := Result.ok.inj h
      have hs : computed = scratch := congrArg Prod.snd hp
      subst computed
      refine ⟨queries, afterQueries, last, rho, claim, hqueries, ?_, hpowers, hclaim, ?_⟩
      · simpa [emptyPayload] using hrho
      · exact (core.result.Result.Ok.inj (congrArg Prod.fst hp)).symm

#print axioms prepare_success
end AspisR1PublicPreparation.PreparedScratchReachability
