import S9ActualPairSharedCallsV1
set_option autoImplicit false
open Aeneas Aeneas.Std Result
open AspisR1S9ProductionPairCutV1
namespace AspisR1S9ActualSharedHighCallsV1
abbrev W := aspis_core.field.wide_exact.WideExact
abbrev Q := aspis_core.field.QM31
abbrev Coeff := Array Q 4#usize
abbrev Row := Array Coeff 5#usize
abbrev Parts := Array W 7#usize
private theorem bind_success {A B : Type} (m : Result A) (next : A → Result B) (out : B)
    (h : (do let x ← m; next x)=.ok out) : ∃ x,m=.ok x ∧ next x=.ok out := by
  cases m with
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h
  | ok x => exact ⟨x,rfl,h⟩

/-- The actual accepted shared-high source call derives both actual high dots,
all four scalar-factor calls and products, and the exact two parts writes.
Rows0/2 supply kinds1/3, rather than incorrectly overwriting parts0/2. -/
theorem shared_high_success_calls (partials : Array W 4#usize) (self : weights.Weights)
    (ap0 ap1 : Array W 4#usize) (parts out : Parts)
    (h : weights.shared_high partials self ap0 ap1 parts=.ok (.Ok (),out)) :
    ∃ (row0 row2 : Row) (high0 high2 f00 f01 f20 f21 : Coeff)
      (dot0 dot2 s00 s01 s20 s21 scale0 scale2 product0 product2 oldPart : W)
      (back : W → Parts),
      Array.index_usize self.factors 0#usize=.ok row0 ∧
      Array.index_usize row0 4#usize=.ok high0 ∧
      weights.high_dot partials high0=.ok (.Ok dot0) ∧
      Array.index_usize row0 0#usize=.ok f00 ∧
      weights.Weights.scalar_factor f00 ap0=.ok s00 ∧
      Array.index_usize row0 1#usize=.ok f01 ∧
      weights.Weights.scalar_factor f01 ap1=.ok s01 ∧
      aspis_core.field.wide_exact.WideExact.mul s00 s01=.ok scale0 ∧
      aspis_core.field.wide_exact.WideExact.mul scale0 dot0=.ok product0 ∧
      Array.index_mut_usize parts 1#usize=.ok (oldPart,back) ∧
      Array.index_usize self.factors 2#usize=.ok row2 ∧
      Array.index_usize row2 4#usize=.ok high2 ∧
      weights.high_dot partials high2=.ok (.Ok dot2) ∧
      Array.index_usize row2 0#usize=.ok f20 ∧
      weights.Weights.scalar_factor f20 ap0=.ok s20 ∧
      Array.index_usize row2 1#usize=.ok f21 ∧
      weights.Weights.scalar_factor f21 ap1=.ok s21 ∧
      aspis_core.field.wide_exact.WideExact.mul s20 s21=.ok scale2 ∧
      aspis_core.field.wide_exact.WideExact.mul scale2 dot2=.ok product2 ∧
      Array.update (back product0) 3#usize product2=.ok out := by
  unfold weights.shared_high at h
  obtain ⟨row0,hrow0,h⟩ := bind_success _ _ _ h
  obtain ⟨high0,hhigh0,h⟩ := bind_success _ _ _ h
  obtain ⟨r0,hdot0,h⟩ := bind_success _ _ _ h
  cases r0 with
  | Err e =>
    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
      core.convert.FromSame.from] at h
    have he : (core.result.Result.Err e : core.result.Result Unit verifier.Error)=.Ok () :=
      congrArg Prod.fst (Result.ok.inj h)
    cases he
  | Ok dot0 =>
    obtain ⟨cf0,hcf0,h⟩ := bind_success
      (core.result.Result.Insts.CoreOpsTry.branch (E:=verifier.Error) (.Ok dot0)) _ _ h
    have he0 : cf0=core.ops.control_flow.ControlFlow.Continue dot0 := (Result.ok.inj hcf0).symm
    cases he0
    obtain ⟨f00,hf00,h⟩ := bind_success _ _ _ h
    obtain ⟨s00,hs00,h⟩ := bind_success _ _ _ h
    obtain ⟨f01,hf01,h⟩ := bind_success _ _ _ h
    obtain ⟨s01,hs01,h⟩ := bind_success _ _ _ h
    obtain ⟨scale0,hscale0,h⟩ := bind_success _ _ _ h
    obtain ⟨product0,hproduct0,h⟩ := bind_success _ _ _ h
    obtain ⟨mutPair,hmut,h⟩ := bind_success _ _ _ h
    rcases mutPair with ⟨oldPart,back⟩
    obtain ⟨row2,hrow2,h⟩ := bind_success _ _ _ h
    obtain ⟨high2,hhigh2,h⟩ := bind_success _ _ _ h
    obtain ⟨r2,hdot2,h⟩ := bind_success _ _ _ h
    cases r2 with
    | Err e =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
      have he : (core.result.Result.Err e : core.result.Result Unit verifier.Error)=.Ok () :=
        congrArg Prod.fst (Result.ok.inj h)
      cases he
    | Ok dot2 =>
      obtain ⟨cf2,hcf2,h⟩ := bind_success
        (core.result.Result.Insts.CoreOpsTry.branch (E:=verifier.Error) (.Ok dot2)) _ _ h
      have he2 : cf2=core.ops.control_flow.ControlFlow.Continue dot2 := (Result.ok.inj hcf2).symm
      cases he2
      obtain ⟨f20,hf20,h⟩ := bind_success _ _ _ h
      obtain ⟨s20,hs20,h⟩ := bind_success _ _ _ h
      obtain ⟨f21,hf21,h⟩ := bind_success _ _ _ h
      obtain ⟨s21,hs21,h⟩ := bind_success _ _ _ h
      obtain ⟨scale2,hscale2,h⟩ := bind_success _ _ _ h
      obtain ⟨product2,hproduct2,h⟩ := bind_success _ _ _ h
      obtain ⟨partsFinal,hupdate,h⟩ := bind_success _ _ _ h
      have hout : partsFinal=out := congrArg Prod.snd (Result.ok.inj h)
      subst partsFinal
      exact ⟨row0,row2,high0,high2,f00,f01,f20,f21,dot0,dot2,s00,s01,s20,s21,
        scale0,scale2,product0,product2,oldPart,back,hrow0,hhigh0,hdot0,hf00,hs00,hf01,hs01,
        hscale0,hproduct0,hmut,hrow2,hhigh2,hdot2,hf20,hs20,hf21,hs21,hscale2,hproduct2,hupdate⟩

#print axioms shared_high_success_calls
end AspisR1S9ActualSharedHighCallsV1
