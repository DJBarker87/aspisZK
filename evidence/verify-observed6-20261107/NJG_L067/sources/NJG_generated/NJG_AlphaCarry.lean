import NJG_RoundDomains
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJG_AlphaCarry
open Aeneas Aeneas.Std Result AspisR1PublicPreparation

theorem canonical_iff (q : aspis_core.field.QM31) : JFv_RoundArithmetic.Canonical q ↔
 SemanticCallSelectedCanonical.SelectedCanonical (SemanticCallSelectedCanonical.toSelected q) := Iff.rfl

theorem set_selected {T : Type} {N : Usize} (a : Array T N) (i : Usize) (bound : i.val<N.val) (q : T) :
 FJb_TailCell.cell (a.set i q) ⟨i.val,bound⟩=q := by
 simp [FJb_TailCell.cell,Array.set]

/-- The newly written active Horner slot is canonical from the SAME actual
semantic child. Before-alpha and before-running need no canonicality premise.
The successful step is an invariant helper input, not a root/row hypothesis. -/
theorem written {H : Type} (R : RoundModel.Boundaries) (D : aspis_core.Digest32 H)
 (pre : r1_wire.Prefix) (before after : r1_wire.SemanticTranscript H)
 (alpha next : Array aspis_core.field.QM31 10#usize) (running value : aspis_core.field.QM31)
 (round : Usize) (bound : round.val<10)
 (step : RoundModel.step R D pre before alpha running round=ok (.Ok (value,next,after))) :
 JFv_RoundArithmetic.Canonical (FJb_TailCell.cell next ⟨round.val,by simpa using bound⟩) := by
 obtain ⟨record,q,getter,sampled,updated⟩:=RoundCalls.step_success R D pre before after alpha next running value round
  (NJG_RoundProducer.row round bound) (NJG_RoundProducer.row_add round bound) step
 have canonical:=SemanticCallSelectedCanonical.semantic_success_selected_canonical D before after record q sampled
 rw [updated,set_selected]
 exact (canonical_iff q).mpr canonical

#print axioms canonical_iff
#print axioms set_selected
#print axioms written
end AspisR1.NJG_AlphaCarry
end
