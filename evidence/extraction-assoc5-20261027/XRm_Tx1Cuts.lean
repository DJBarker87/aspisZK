import XRk_PrepareProjection
import XRm_PowersCanonical
import XRm_CompactShape
open Aeneas Aeneas.Std Result
open XRk_Release XRk_ResultTools
namespace XRm_Tx1Cuts
abbrev E := aspis_core.field.wide_exact.WideExact
theorem cuts {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (physical proof : Slice U8) (split : Usize) (hash : H)
    (obs : Option (verifier.Phase → Result Unit)) (bytes : alloc.vec.Vec U8)
    (run : verifier.candidate.tx1 D pub physical proof split hash obs=ok (.Ok bytes)) :
    ∃ (p : verifier.Prepared) (scratch : Array E 29#usize) (zero : E) (a : verifier.Accumulator) (shape : transport.Variant),
      verifier.candidate.parse_shape proof=ok (.Ok shape) ∧ shape=.S2 ∧
      verifier.candidate.canonical_scan proof=ok (.Ok ()) ∧
      aspis_core.field.wide_exact.WideExact.ZERO=ok zero ∧
      verifier.candidate.prepare D pub proof hash obs (Array.repeat 29#usize zero)=ok (.Ok p,scratch) ∧
      split=compact.SPLIT ∧ weights.powers 29#usize p.gamma=ok scratch ∧
      (∀ e ∈ scratch.val, XRm_WideProducer.Canonical e) ∧
      verifier.checkpoint D p a proof physical hash=ok bytes := by
  unfold verifier.candidate.tx1 at run
  split at run
  · cases run
  · rename_i valid
    have split_eq : split=compact.SPLIT := by
      simpa only [bne_iff_ne,not_not] using valid
    obtain ⟨r,hshape,run⟩ := bind_success _ _ _ run
    cases r with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
        core.convert.FromSame.from,bind_tc_ok] at run
      cases run
    | Ok shapeUnit =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
      obtain ⟨r,hscan,run⟩ := bind_success _ _ _ run
      cases r with
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry.branch,
          core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
          core.convert.FromSame.from,bind_tc_ok] at run
        cases run
      | Ok scanUnit =>
        cases scanUnit
        simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
        obtain ⟨unit,_,run⟩ := bind_success _ _ _ run
        obtain ⟨zero,hzero,run⟩ := bind_success _ _ _ run
        obtain ⟨r,scratch,hprepare,run⟩ := pair_bind_success _ _ _ run
        cases r with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,
            core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
            core.convert.FromSame.from,bind_tc_ok] at run
          cases run
        | Ok p =>
          simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
          obtain ⟨r,_,run⟩ := bind_success _ _ _ run
          cases r with
          | Err error =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,
              core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
              core.convert.FromSame.from,bind_tc_ok] at run
            cases run
          | Ok initial =>
            simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
            obtain ⟨unit,_,run⟩ := bind_success _ _ _ run
            obtain ⟨offRoot,_,run⟩ := bind_success _ _ _ run
            obtain ⟨offRound1,_,run⟩ := bind_success _ _ _ run
            obtain ⟨rootSlice,_,run⟩ := bind_success _ _ _ run
            obtain ⟨rootResult,_,run⟩ := bind_success _ _ _ run
            obtain ⟨root,_,run⟩ := bind_success _ _ _ run
            obtain ⟨r,_,run⟩ := bind_success _ _ _ run
            cases r with
            | Err error =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,
                core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                core.convert.FromSame.from,bind_tc_ok] at run
              cases run
            | Ok merkleUnit =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
              obtain ⟨unit,_,run⟩ := bind_success _ _ _ run
              obtain ⟨r,_,run⟩ := bind_success _ _ _ run
              cases r with
              | Err error =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,
                  core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                  core.convert.FromSame.from,bind_tc_ok] at run
                cases run
              | Ok geometry =>
                simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                obtain ⟨r,_,run⟩ := bind_success _ _ _ run
                cases r with
                | Err error =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,
                    core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                    core.convert.FromSame.from,bind_tc_ok] at run
                  cases run
                | Ok pending0 =>
                  simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                  obtain ⟨r,_,run⟩ := bind_success _ _ _ run
                  cases r with
                  | Err error =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,
                      core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual,
                      core.convert.FromSame.from,bind_tc_ok] at run
                    cases run
                  | Ok result =>
                    simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok] at run
                    rcases result with ⟨a,pending⟩
                    try simp only [lift,bind_tc_ok] at run
                    obtain ⟨values,_,run⟩ := bind_success _ _ _ run
                    obtain ⟨sourceBytes,hcheckpoint,run⟩ := bind_success _ _ _ run
                    obtain ⟨unit,_,run⟩ := bind_success _ _ _ run
                    have same : sourceBytes=bytes := core.result.Result.Ok.inj (Result.ok.inj run)
                    obtain ⟨sem,view,hconstructor⟩ := XRk_PrepareProjection.constructor D pub proof hash obs
                      (Array.repeat 29#usize zero) scratch p hprepare
                    have hpowers := XRk_ScratchProjection.accepted_powers D sem view hash
                      (Array.repeat 29#usize zero) scratch p hconstructor
                    have canonical := XRm_PowersCanonical.powers p.gamma scratch hpowers
                    exact ⟨p,scratch,zero,_,shapeUnit,hshape,(XRm_CompactShape.accepted proof shapeUnit hshape).1,
                      hscan,hzero,hprepare,split_eq,hpowers,canonical,hcheckpoint.trans (congrArg Result.ok same)⟩
#print axioms cuts
end XRm_Tx1Cuts
