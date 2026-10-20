import AspisR1Stage2AdoptedResume.Funs
import Stage2GeneratedPrefixSuccessInversion

set_option autoImplicit false
open Aeneas Aeneas.Std Result

namespace AspisR1Stage2AdoptedReader.GeneratedPrefixCallSuccess

abbrev GReader := AspisR1Stage2AdoptedResume.verifier.Reader
abbrev GWide := AspisR1Stage2AdoptedResume.aspis_core.field.WideExact
abbrev GQM := AspisR1Stage2AdoptedResume.aspis_core.field.QM31

private theorem bind_success {A B : Type} (m : Result A) (k : A → Result B) (v : B)
    (h : (do let x ← m; k x) = ok v) : ∃ x, m = ok x ∧ k x = ok v := by
  cases m with
  | ok x => exact ⟨x, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

private theorem let_pair_prod {A B C : Type} (x : A) (y : B) (f : A → B → C) :
    (let (a, b) := (x, y); f a b) = f x y := rfl

private theorem bind_pair_success {A B C : Type} (m : Result (A × B))
    (k : A → B → Result C) (v : C)
    (h : (do let (a, b) ← m; k a b) = ok v) :
    ∃ a b, m = ok (a, b) ∧ k a b = ok v := by
  cases m with
  | ok pair => rcases pair with ⟨a, b⟩; exact ⟨a, b, rfl, h⟩
  | fail e => simp only [bind_tc_fail] at h; cases h
  | div => simp only [bind_tc_div] at h; cases h

theorem generated_prefix_call_success
    (bytes : Slice Std.U8)
    (state root0 root1 : Array Std.U8 32#usize)
    (gamma kappa alpha0 alpha1 : GWide) (rho : GQM) (finalAt : Usize)
    (h : AspisR1Stage2AdoptedResume.verifier.resume_read_prefix bytes =
      ok (.Ok (state, Array.make 2#usize [root0, root1], gamma, kappa,
        Array.make 2#usize [alpha0, alpha1], rho, finalAt))) :
    ∃ r1 r2 r3 r4 r5 r6 r7 r8,
      AspisR1Stage2AdoptedResume.verifier.Reader.raw 32#usize
        { bytes, «at» := 80#usize } = ok (state, r1) ∧
      AspisR1Stage2AdoptedResume.verifier.Reader.raw 32#usize r1 = ok (root0, r2) ∧
      AspisR1Stage2AdoptedResume.verifier.Reader.raw 32#usize r2 = ok (root1, r3) ∧
      AspisR1Stage2AdoptedResume.verifier.Reader.e r3 = ok (.Ok gamma, r4) ∧
      AspisR1Stage2AdoptedResume.verifier.Reader.e r4 = ok (.Ok kappa, r5) ∧
      AspisR1Stage2AdoptedResume.verifier.Reader.e r5 = ok (.Ok alpha0, r6) ∧
      AspisR1Stage2AdoptedResume.verifier.Reader.e r6 = ok (.Ok alpha1, r7) ∧
      AspisR1Stage2AdoptedResume.verifier.Reader.k r7 = ok (.Ok rho, r8) ∧
      r8.«at» = finalAt := by
  unfold AspisR1Stage2AdoptedResume.verifier.resume_read_prefix at h
  obtain ⟨state', r1, hp0, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨root0', r2, hp1, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨root1', r3, hp2, h⟩ := bind_pair_success _ _ _ h
  obtain ⟨res3, r4, hp3, h⟩ := bind_pair_success _ _ _ h
  cases res3 with
  | Err err =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        bind_tc_ok,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from] at h
      cases h
  | Ok gamma' =>
      have hbranch3 : core.result.Result.Insts.CoreOpsTry.branch
          (core.result.Result.Ok gamma') =
          ok (core.ops.control_flow.ControlFlow.Continue gamma' :
            core.ops.control_flow.ControlFlow
              (core.result.Result core.convert.Infallible
                AspisR1Stage2AdoptedResume.verifier.Error) GWide) := rfl
      rw [hbranch3, bind_tc_ok] at h
      obtain ⟨res4, r5, hp4, h⟩ := bind_pair_success _ _ _ h
      cases res4 with
      | Err err =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            bind_tc_ok,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from] at h
          cases h
      | Ok kappa' =>
          have hbranch4 : core.result.Result.Insts.CoreOpsTry.branch
              (core.result.Result.Ok kappa') =
              ok (core.ops.control_flow.ControlFlow.Continue kappa' :
                core.ops.control_flow.ControlFlow
                  (core.result.Result core.convert.Infallible
                    AspisR1Stage2AdoptedResume.verifier.Error) GWide) := rfl
          rw [hbranch4, bind_tc_ok] at h
          obtain ⟨res5, r6, hp5, h⟩ := bind_pair_success _ _ _ h
          cases res5 with
          | Err err =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                bind_tc_ok,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from] at h
              cases h
          | Ok alpha0' =>
              have hbranch5 : core.result.Result.Insts.CoreOpsTry.branch
                  (core.result.Result.Ok alpha0') =
                  ok (core.ops.control_flow.ControlFlow.Continue alpha0' :
                    core.ops.control_flow.ControlFlow
                      (core.result.Result core.convert.Infallible
                        AspisR1Stage2AdoptedResume.verifier.Error) GWide) := rfl
              rw [hbranch5, bind_tc_ok] at h
              obtain ⟨res6, r7, hp6, h⟩ := bind_pair_success _ _ _ h
              cases res6 with
              | Err err =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    bind_tc_ok,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from] at h
                  cases h
              | Ok alpha1' =>
                  have hbranch6 : core.result.Result.Insts.CoreOpsTry.branch
                      (core.result.Result.Ok alpha1') =
                      ok (core.ops.control_flow.ControlFlow.Continue alpha1' :
                        core.ops.control_flow.ControlFlow
                          (core.result.Result core.convert.Infallible
                            AspisR1Stage2AdoptedResume.verifier.Error) GWide) := rfl
                  rw [hbranch6, bind_tc_ok] at h
                  obtain ⟨res7, r8, hp7, h⟩ := bind_pair_success _ _ _ h
                  cases res7 with
                  | Err err =>
                      simp only [core.result.Result.Insts.CoreOpsTry.branch,
                        bind_tc_ok,
                        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                        core.convert.FromSame.from] at h
                      cases h
                  | Ok rho' =>
                      have hbranch7 : core.result.Result.Insts.CoreOpsTry.branch
                          (core.result.Result.Ok rho') =
                          ok (core.ops.control_flow.ControlFlow.Continue rho' :
                            core.ops.control_flow.ControlFlow
                              (core.result.Result core.convert.Infallible
                                AspisR1Stage2AdoptedResume.verifier.Error) GQM) := rfl
                      rw [hbranch7, bind_tc_ok] at h
                      simp only [Result.ok.injEq,
                        core.result.Result.Ok.injEq,
                        Prod.mk.injEq] at h
                      rcases h with ⟨rfl, hroots, hgamma, hkappa, halphas, hrho, hat⟩
                      rcases hroots with ⟨rfl, rfl⟩
                      rcases halphas with ⟨rfl, rfl⟩
                      subst gamma
                      subst kappa
                      subst rho
                      subst finalAt
                      exact ⟨r1,r2,r3,r4,r5,r6,r7,r8,hp0,hp1,hp2,hp3,hp4,hp5,hp6,hp7,rfl⟩

#print axioms generated_prefix_call_success

end AspisR1Stage2AdoptedReader.GeneratedPrefixCallSuccess
