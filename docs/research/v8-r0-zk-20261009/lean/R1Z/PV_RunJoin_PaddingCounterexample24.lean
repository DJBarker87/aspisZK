import R1Z.PV_RunJoin_PremiseTruth24
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_PaddingCounterexample24
open Aeneas Aeneas.Std PV_Src_NativeInput
open BuilderForestAdmissionPort.pool_v1
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K] [CharP K 2147483647]

/-- Short constant columns, deliberately not compiler output. -/
def ones : alloc.vec.Vec U32 := ⟨List.replicate 14 1#u32, by simp; scalar_tac⟩
def columns : Array (alloc.vec.Vec U32) 16#usize :=
  BuilderRecordsArray.tabulate 16#usize (fun _ => ones)

/-- Same admitted transfer arguments and public transition; only cached
semantic columns are replaced. Raw source.Instance permits this value. -/
def bad : Input :=
  {PV_RunJoin_AdmittedCarrier23.transfer with compiled :=
    {PV_RunJoin_AdmittedCarrier23.transfer.compiled with semantic_c1 := {c1 := columns}}}

theorem admitted : PV_RunJoin_UniversalBuild22.Admission (K := K) bad :=
  PV_RunJoin_AdmittedCarrier23.transfer_admitted
#print axioms admitted

theorem public_eq :
    (PV_RunJoin_PremiseTruth24.raw (K := K)).public bad =
      BuilderSource.prover.public
        (PV_RunJoin_UniversalBuild22.toInstance (fun _ : Unit => bad)
          (fun _ => admitted) ()) :=
  PV_RunJoin_UniversalBuild22.public_eq _ _ _ ()
#print axioms public_eq

/-- A symbolic padding lemma: no recurrence state or hash is evaluated. -/
theorem model_padding (pub : R0P.Public K) (w : R0Z.BuilderModel.ModelWitness K) :
    R0Z.BuilderModel.buildModel pub w 0 13 = 0 := by
  change R0Z.BuilderModel.layout _ 0 13 = 0
  rw [R0Z.BuilderModel.layout_block _ 0 13 (by decide) 0 rfl]
  rfl
#print axioms model_padding

theorem canonical_padding (w : BuilderCanonical.Instance (K := K)) :
    BuilderSource.prover.build w 0 13 = 0 := by
  change BuilderRefinement.mergedTrace _ _ 0 13 = 0
  rw [BuilderCanonical.canonical_trace]
  exact model_padding _ _
#print axioms canonical_padding

theorem bad_cell : (PV_RunJoin_PremiseTruth24.raw (K := K)).build bad 0 13 = 1 := by
  change R0Z.WriterRefine.liftU (PV_Src_Forest_Columns.read columns 0 13) = (1 : K)
  unfold PV_Src_Forest_Columns.read
  rw [if_pos (by decide)]
  change R0Z.WriterRefine.liftU
    ((BuilderRecordsArray.tabulate 16#usize (fun _ => ones)).val[0]!).val[13]! = (1 : K)
  rw [BuilderRecordsArray.tabulate_get _ _ _ (by decide)]
  change R0Z.WriterRefine.liftU (List.replicate 14 1#u32)[13]! = (1 : K)
  simp only [List.getElem!_replicate,show 13 < 14 by decide,if_true]
  rfl
#print axioms bad_cell

/-- V153 is false here for EVERY canonical target, regardless of map. -/
theorem build_eq_false (w : BuilderCanonical.Instance (K := K)) :
    (PV_RunJoin_PremiseTruth24.raw (K := K)).build bad ≠ BuilderSource.prover.build w := by
  intro h
  have cell := congrFun (congrFun h 0) 13
  rw [bad_cell,canonical_padding] at cell
  exact one_ne_zero cell
#print axioms build_eq_false

theorem universal_build_eq_false (f : Input → BuilderCanonical.Instance (K := K)) :
    ¬ (∀ i : Input, (PV_RunJoin_PremiseTruth24.raw (K := K)).build i =
      BuilderSource.prover.build (f i)) := by
  intro h
  exact build_eq_false (f bad) (h bad)
#print axioms universal_build_eq_false

theorem identification_unsatisfiable (f : Input → BuilderCanonical.Instance (K := K)) :
    ¬ BuilderSource.SourceIdentification (PV_RunJoin_PremiseTruth24.raw (K := K)) f := by
  intro h
  exact universal_build_eq_false f h.build_eq
#print axioms identification_unsatisfiable

/-- The failure persists when semantic admission alone restricts the carrier. -/
theorem admitted_identification_unsatisfiable
    (f : PV_RunJoin_AdmittedCarrier23.Admitted (K := K) → BuilderCanonical.Instance (K := K)) :
    ¬ BuilderSource.SourceIdentification
      (PV_Src_NativeIdentification.prover (K := K)
        (fun i : PV_RunJoin_AdmittedCarrier23.Admitted (K := K) => i.val)
        PV_Src_Transport.transport) f := by
  intro h
  exact build_eq_false (f ⟨bad,admitted⟩) (h.build_eq ⟨bad,admitted⟩)
#print axioms admitted_identification_unsatisfiable
end R1Z.PV_RunJoin_PaddingCounterexample24
