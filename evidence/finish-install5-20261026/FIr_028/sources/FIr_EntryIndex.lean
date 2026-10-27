import FIq_TypedData
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIr_EntryIndex
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open RawActualAnnotatedPolynomialRun

theorem length {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    {initial final : Outcome H} {entries : List (RoundEvidence D pre)}
    (run : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule initial final entries) :
    entries.length=10 := by
  have h := congrArg List.length (RawActualAnnotatedTypedRows.annotated_events run)
  simpa only [List.length_map,SemanticRoundsCheckedTrace.schedule,List.length_cons,List.length_nil] using h

theorem round {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    {initial final : Outcome H} {entries : List (RoundEvidence D pre)}
    (run : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule initial final entries)
    (j : Fin 10) : (entries[j.val]'(by rw [length run];exact j.isLt)).round.val=j.val := by
  have schedule : SemanticRoundsCheckedTrace.schedule.map (fun p=>p.1.val)=List.range 10 := rfl
  have indices : entries.map (fun entry=>entry.round.val)=List.range 10 := by
    rw [← schedule,← RawActualAnnotatedTypedRows.annotated_events run,List.map_map]
    rfl
  have slot := congrArg (fun xs : List Nat=>xs[j.val]?) indices
  simpa only [List.getElem?_map,List.getElem?_eq_getElem (by rw [length run];exact j.isLt),
    List.getElem?_range,if_pos j.isLt,Option.map_some,Option.some.injEq] using slot

theorem challenge {H : Type} {D : aspis_core.Digest32 H} {pre : r1_wire.Prefix}
    {initial final : Outcome H} {entries : List (RoundEvidence D pre)}
    (run : AnnotatedRun D pre SemanticRoundsCheckedTrace.schedule initial final entries)
    (alpha : Array aspis_core.field.QM31 10#usize)
    (same : entries.map RoundEvidence.q=alpha.val) (j : Fin 10) :
    (entries[j.val]'(by rw [length run];exact j.isLt)).q=
      alpha.val[j.val]'(by have len := alpha.property;change alpha.val.length=10 at len;omega) := by
  have slot := congrArg (fun xs : List aspis_core.field.QM31=>xs[j.val]?) same
  simpa only [List.getElem?_map,List.getElem?_eq_getElem (by rw [length run];exact j.isLt),
    List.getElem?_eq_getElem (by have len := alpha.property;change alpha.val.length=10 at len;omega),
    Option.map_some,Option.some.injEq] using slot

#print axioms length
#print axioms round
#print axioms challenge
end AspisR1.FIr_EntryIndex
end
