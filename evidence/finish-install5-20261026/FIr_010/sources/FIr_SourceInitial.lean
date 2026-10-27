import FIq_TypedData
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_SourceInitial
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualAnnotatedPolynomialRun

theorem head_state {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    {events : List (Usize × U8)} {initial final : Outcome H}
    {entry : RoundEvidence D pre} {rest : List (RoundEvidence D pre)}
    (run : AnnotatedRun D pre events initial final (entry::rest)) :
    entry.beforeState=initial := by
  cases run
  rfl

theorem first_boundary {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
    (initial final : RawActualAnnotatedPolynomialRun.Outcome H)
    (entries : List (RoundEvidence D pre))
    (run : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule initial final entries)
    (values : SemanticPrefixCodec.Full)
    (full : SemanticPrefixCodec.encodeFull values=PrefixAdapter.completedRecords pre) :
    (SemanticCoefficientCodec.polynomial (SemanticPayloadView.coeffAt values 0)).eval 0+
      (SemanticCoefficientCodec.polynomial (SemanticPayloadView.coeffAt values 0)).eval 1=
      algebraMap ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact (DecodeMain initial.1) := by
  have events := RawActualAnnotatedTypedRows.annotated_events run
  cases entries with
  | nil => simp only [List.map_nil,SemanticRoundsCheckedTrace.schedule] at events;cases events
  | cons entry rest =>
    have first : entry.round=0#usize := by
      exact congrArg Prod.fst (List.cons.inj events).1
    have poly := FIq_TypedPolynomials.same_entry (⟨[],by simp⟩ : Slice U8) pre values full
      D initial final (entry::rest) run entry List.mem_cons_self
    have ix : (⟨entry.round.val,RawActualAnnotatedTypedRows.entry_schedule_round_lt run entry List.mem_cons_self⟩ : Fin 10)=0 :=
      Fin.ext (by simpa using congrArg (fun u : Usize => u.val) first)
    rw [ix] at poly
    have boundary : (polynomialOf entry.coefficients).eval 0+
        (polynomialOf entry.coefficients).eval 1=DecodeMain initial.1 := by
      rw [← head_state run]
      exact entry.boundary
    have mapped := congrArg
      (algebraMap ExtractedMaskQM31Exact.QM31Exact AspisWideTower.WideExact) boundary
    rw [map_add] at mapped
    rw [← poly]
    simpa only [Polynomial.eval_map_algebraMap,map_zero,map_one] using mapped

#print axioms head_state
#print axioms first_boundary
end AspisR1.FIr_SourceInitial
end
