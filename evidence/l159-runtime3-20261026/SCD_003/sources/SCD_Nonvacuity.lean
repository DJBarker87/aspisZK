import SCD_Carrier
import CPH_Nonvacuity
set_option autoImplicit false
noncomputable section
namespace AspisR1.SCD_Nonvacuity
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open CPG_Projection CPH_FixtureData
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw
open F3T_Experiment F3T_ByteCarrier

/-- Joint witness includes the exact TWO entry admissions omitted from SCC's
stated joint conclusion, sdk/std, both wrappers, all four game clauses and
persistence. Canonical stored identity holds simultaneously. The local natives
are NOT the installed crypto extraction instance; no full Rc5 inhabitation
or actual deployed attack is asserted. -/
theorem admitted_game_with_unassociated {F C : Type}
    (c : DrvC_Installation.Configuration F C) (P : ByteProver) (H : Bytes → State)
    (data1 data2 : Slice U8) (slot : S2W_ExtractionBoundary.Slot) :
    S2TrustedSdkBorrow (model (Nat → Record)) ∧
    S2W_TrustedStd.TrustedStd copy ∧
    Nonempty (S2W_D189Consolidation.RuntimeEntrypointAdmission
      (model (Nat → Record)) e1 e1.heap 3) ∧
    Nonempty (S2W_D189Consolidation.RuntimeEntrypointAdmission
      (model (Nat → Record)) e2 e2.heap 7) ∧
    CPH_Game.DeployedPairExecution observations false true e1 e2 saved suffix
      n1 n2 copy allocator id ∧
    CPR_DataPersistence.TwoTransactionLaw
      (adjacent observations) (ordinary observations (Hist_Nonvacuity.key 0#u8))
      (before observations) (tentative observations) (success observations) (loaded observations) ∧
    first n1 copy allocator e1 id data1 () = ok (.Ok (saved,CPH_FixtureWrappers.post1,())) ∧
    second n2 allocator e2 id data2 slot () = ok (.Ok (e2.heap,())) ∧
    observations.physicalEvents false ≠ [] ∧
    (eval H (F3T_Canon.canon (lift c P))).2.stored = (eval H P).2.stored ∧
    ∃ (runtime : F3T_Runtime.Runtime) (run : RunView),
      eval H runtime = ([],some run) ∧ run.2.2 = true ∧
      run.2.1.stored ≠ (eval H P).2.stored ∧
      ¬ SCD_Carrier.ByteObservation P runtime ∧
      (∀ rust : F3T_TwoPass.Verifier,
        ¬ SCC_Physical.FirstPassBinding rust (F3T_Canon.canon (lift c P)) runtime) := by
  obtain ⟨sdk,std,a1,a2,game,persistence,accepted1,accepted2,_,events,_⟩ :=
    CPH_Nonvacuity.joint_runtime data1 data2 slot
  refine ⟨sdk,std,a1,a2,game,persistence,accepted1,accepted2,events,
    SCD_Carrier.canonical_stored c P H,?_⟩
  obtain ⟨runtime,run,observed,accepted,different,notStored,notFirst⟩ :=
    SCC_Physical.accepted_unassociated (F3T_Canon.canon (lift c P)) H
  have unequal : run.2.1.stored ≠ (eval H P).2.stored := by
    simpa only [SCD_Carrier.canonical_stored] using different
  refine ⟨runtime,run,observed,accepted,unequal,?_,notFirst⟩
  intro observation
  exact notStored ((SCD_Carrier.stored_iff_observation c P runtime).mpr observation)

#print axioms admitted_game_with_unassociated
#print admitted_game_with_unassociated
end AspisR1.SCD_Nonvacuity
end
