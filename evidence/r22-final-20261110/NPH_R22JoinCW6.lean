import NPH_R22JoinCW5
import RPz7_F3M_InactiveCanonical
import NNH_Run5bPreparedCore
import CurrentCompactCallerModelV1

/-! NPH_ (R22, CW step 5): the tx1 candidate.prepare from its entry to the op8 (prepare) call.
- `candidate_op8_congr`: for any Ops O whose op5 is the selected source view, replacing op8 by
  any f that agrees with O.op8 on views returned by a successful source view leaves
  candidate.prepare unchanged. So every op8 call executes on a view v with
  sourceView proof s4 s5 = ok (.Ok v). Bind-stepping through the candidate.prepare body.
- `deployed_prepare_guarded`: with op5 = sourceView and op8 = the deployed originalNew
  (withOriginalSerializer closedSampling, Total.embed), candidate.prepare equals the same
  body whose op8 is NPH_R22JoinCW5.guardedNew, i.e. whose claim boundary runs the borrowed
  claim only on canonical kappa and inactive. inactive: F3M_InactiveCanonical.source; kappa:
  NPH_R22JoinCW5.deployed_kappa.
- `installed_prepare_guarded`: the same for DrvC_Installation.currentInstalled cfg, every
  configuration (op5 and op8 slots by rfl and NNH_Run5bPreparedCore.installed).
Standard axioms. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.NPH_R22JoinCW6
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller
open AspisR1.NPH_R22JoinCW5 (bind_congr_ok)

abbrev Op8 := ∀ {H : Type}, aspis_core.digest.Digest32 H → r1_semantic.Verified H → verifier.View → H →
  Array aspis_core.field.wide_exact.WideExact 29#usize →
  Result ((core.result.Result verifier.Prepared verifier.Error) ×
    Array aspis_core.field.wide_exact.WideExact 29#usize)

theorem ls_eq (O : Ops) (f : Op8) :
    compact.LOGICAL_SEMANTIC { O with op8 := f } = compact.LOGICAL_SEMANTIC O := by
  unfold compact.LOGICAL_SEMANTIC; rfl
theorem os_eq (O : Ops) (f : Op8) :
    compact.OFF_SEMANTIC { O with op8 := f } = compact.OFF_SEMANTIC O := by
  unfold compact.OFF_SEMANTIC; rfl
theorem oy_eq (O : Ops) (f : Op8) :
    compact.OFF_Y1 { O with op8 := f } = compact.OFF_Y1 O := by
  unfold compact.OFF_Y1 compact.OFF_SEMANTIC; rfl
theorem oi_eq (O : Ops) (f : Op8) :
    compact.OFF_INACTIVE { O with op8 := f } = compact.OFF_INACTIVE O := by
  unfold compact.OFF_INACTIVE compact.OFF_Y1 compact.OFF_SEMANTIC; rfl

theorem candidate_op8_congr (O : Ops) (f : Op8)
    (hop5 : ∀ p s y, O.op5 p s y = InstalledPreparation.sourceView p s y)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize)
    (hagree : ∀ (sem : r1_semantic.Verified H) (v : verifier.View) (p s y : Slice U8),
      InstalledPreparation.sourceView p s y = ok (.Ok v) →
      f D sem v hash g = O.op8 D sem v hash g) :
    verifier.candidate.prepare { O with op8 := f } D pub proof hash obs g =
      verifier.candidate.prepare O D pub proof hash obs g := by
  unfold verifier.candidate.prepare
  rw [ls_eq, os_eq, oy_eq, oi_eq]
  refine bind_congr_ok _ _ _ (fun i _ => ?_)
  refine bind_congr_ok _ _ _ (fun i1 _ => ?_)
  refine bind_congr_ok _ _ _ (fun i2 _ => ?_)
  refine bind_congr_ok _ _ _ (fun r _ => ?_)
  refine bind_congr_ok _ _ _ (fun r1 _ => ?_)
  refine bind_congr_ok _ _ _ (fun cf _ => ?_)
  cases cf with
  | Break residual => rfl
  | Continue val =>
    refine bind_congr_ok _ _ _ (fun sd _ => ?_)
    obtain ⟨s, back⟩ := sd
    refine bind_congr_ok _ _ _ (fun sp _ => ?_)
    obtain ⟨⟨semantic, y1⟩, back2⟩ := sp
    refine bind_congr_ok _ _ _ (fun i3 _ => ?_)
    refine bind_congr_ok _ _ _ (fun i4 _ => ?_)
    refine bind_congr_ok _ _ _ (fun s1 _ => ?_)
    refine bind_congr_ok _ _ _ (fun rs _ => ?_)
    obtain ⟨r2, semantic1⟩ := rs
    refine bind_congr_ok _ _ _ (fun cf1 _ => ?_)
    cases cf1 with
    | Break residual => rfl
    | Continue u =>
      refine bind_congr_ok _ _ _ (fun i5 _ => ?_)
      refine bind_congr_ok _ _ _ (fun s2 _ => ?_)
      refine bind_congr_ok _ _ _ (fun ry _ => ?_)
      obtain ⟨r3, y11⟩ := ry
      refine bind_congr_ok _ _ _ (fun cf2 _ => ?_)
      cases cf2 with
      | Break residual => rfl
      | Continue u2 =>
        refine bind_congr_ok _ _ _ (fun s4 _ => ?_)
        refine bind_congr_ok _ _ _ (fun s5 _ => ?_)
        refine bind_congr_ok _ _ _ (fun r4 h5 => ?_)
        have hv : InstalledPreparation.sourceView proof s4 s5 = ok r4 := by
          rw [← hop5]; exact h5
        refine bind_congr_ok _ _ _ (fun cf3 h3 => ?_)
        cases cf3 with
        | Break residual => rfl
        | Continue v =>
          have hr4 : r4 = .Ok v := by
            cases r4 with
            | Ok w =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch] at h3
              cases h3
              rfl
            | Err e =>
              simp only [core.result.Result.Insts.CoreOpsTry.branch] at h3
              cases h3
          rw [hr4] at hv
          refine bind_congr_ok _ _ _ (fun r5 _ => ?_)
          refine bind_congr_ok _ _ _ (fun r6 _ => ?_)
          refine bind_congr_ok _ _ _ (fun cf4 _ => ?_)
          cases cf4 with
          | Break residual => rfl
          | Continue val2 =>
            refine bind_congr_ok _ _ _ (fun u3 _ => ?_)
            exact hagree val2 v proof s4 s5 hv

/-- The deployed op8 with the guarded claim boundary. -/
def guardedOp8 : Op8 := fun D sem v hash g => AspisR1.NPH_R22JoinCW5.guardedNew
  (OriginalSerializerInstallation.withOriginalSerializer BorrowedClaimPrepared.closedSampling)
  AspisS1M31Embedding.Total.embed D sem v hash g

theorem deployed_prepare_guarded (O : Ops)
    (hop5 : ∀ p s y, O.op5 p s y = InstalledPreparation.sourceView p s y)
    (hop8 : ∀ {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
      (v : verifier.View) (hash : H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize),
      O.op8 D sem v hash g = BorrowedClaimPrepared.originalNew
        (OriginalSerializerInstallation.withOriginalSerializer BorrowedClaimPrepared.closedSampling)
        AspisS1M31Embedding.Total.embed D sem v hash g)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    verifier.candidate.prepare O D pub proof hash obs g =
      verifier.candidate.prepare { O with op8 := guardedOp8 } D pub proof hash obs g := by
  symm
  apply candidate_op8_congr O _ hop5
  intro sem v p s y hv
  rw [hop8]
  exact (AspisR1.NPH_R22JoinCW5.originalNew_guarded _ _ D sem v hash g
    (AspisR1.F3M_InactiveCanonical.source p s y v hv)).symm

theorem installed_op5 {F C : Type} (cfg : AspisR1.DrvC_Installation.Configuration F C) (p s y : Slice U8) :
    (AspisR1.DrvC_Installation.currentInstalled cfg).op5 p s y = InstalledPreparation.sourceView p s y := rfl

theorem installed_op8 {F C : Type} (cfg : AspisR1.DrvC_Installation.Configuration F C)
    {H : Type} (D : aspis_core.digest.Digest32 H) (sem : r1_semantic.Verified H)
    (v : verifier.View) (hash : H) (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    (AspisR1.DrvC_Installation.currentInstalled cfg).op8 D sem v hash g =
      BorrowedClaimPrepared.originalNew
        (OriginalSerializerInstallation.withOriginalSerializer BorrowedClaimPrepared.closedSampling)
        AspisS1M31Embedding.Total.embed D sem v hash g := by
  have e : (AspisR1.DrvC_Installation.currentInstalled cfg).op8 D sem v hash g =
      (BorrowedClaimPrepared.closedInstall (AspisR1.DrvC_Installation.currentInstalled cfg)).op8
        D sem v hash g := rfl
  rw [e]
  exact AspisR1.NNH_Run5bPreparedCore.installed _ D sem v hash g

theorem installed_prepare_guarded {F C : Type} (cfg : AspisR1.DrvC_Installation.Configuration F C)
    {H : Type} (D : aspis_core.digest.Digest32 H)
    (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (hash : H) (obs : Option (verifier.Phase → Result Unit))
    (g : Array aspis_core.field.wide_exact.WideExact 29#usize) :
    verifier.candidate.prepare (AspisR1.DrvC_Installation.currentInstalled cfg) D pub proof hash obs g =
      verifier.candidate.prepare { AspisR1.DrvC_Installation.currentInstalled cfg with op8 := guardedOp8 }
        D pub proof hash obs g :=
  deployed_prepare_guarded _ (installed_op5 cfg) (fun D sem v hash g => installed_op8 cfg D sem v hash g)
    D pub proof hash obs g

#print axioms ls_eq
#print axioms os_eq
#print axioms oy_eq
#print axioms oi_eq
#print axioms candidate_op8_congr
#print axioms guardedOp8
#print axioms deployed_prepare_guarded
#print axioms installed_op5
#print axioms installed_op8
#print axioms installed_prepare_guarded
end AspisR1.NPH_R22JoinCW6
