import R1Z.PV_Canon_Prefix
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result ProverRwFull
/-- An exact extracted successful prefix, with computational source equations.
No canonicality field occurs in this carrier. -/
structure ExtractedPrefix (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base)) where
  H : Type
  digest : aspis_core.digest.Digest32 H
  before : host_wire.SemanticTranscript H
  after : host_wire.SemanticTranscript H
  tag : U8
  framed : Slice U8
  values : Array aspis_core.field.QM31 28#usize
  coefficients : Array aspis_core.field.QM31 28#usize
  point : Array aspis_core.field.QM31 10#usize
  updated : Array aspis_core.field.QM31 10#usize
  round : Usize
  sampled : aspis_core.field.QM31
  read : aspis_core.field.QM31
  round_lt : round.val < 10
  interpolation : @host_sumcheck.interpolate (PV_Join_PublicCaller.native base)
    (PV_Join_PublicCaller.selected base ops) values = .ok coefficients
  semantic : @host_wire.SemanticTranscript.semantic (PV_Join_PublicCaller.native base)
    (PV_Join_PublicCaller.selected base ops) H digest before tag framed = .ok (.Ok sampled,after)
  update : Array.update point round sampled = .ok updated
  readback : Array.index_usize updated round = .ok read
/-- Exact P obligation on native reachability, NOT a trust item: the actual
records/prover host_sumcheck op121 event must supply this extracted prefix
with the same coefficient array and challenge. Shipped locations are in
OBLIGATIONS.md; this file provides no native trace instance. -/
def P_NativePrefixBinding (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    (reached : Array aspis_core.field.QM31 28#usize → aspis_core.field.QM31 → Prop) : Prop :=
  ∀ p q, reached p q → ∃ e : ExtractedPrefix base ops, e.coefficients=p ∧ e.read=q
 theorem extracted_prefix_canonical (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base)) (e : ExtractedPrefix base ops) :
    Coeffs e.coefficients ∧ Q e.read :=
  op121_arguments base ops e.digest e.before e.after e.tag e.framed e.values e.coefficients
    e.point e.updated e.round e.sampled e.read e.round_lt e.interpolation e.semantic e.update e.readback
 theorem reached_canonical (base : ExternalTypes)
    (ops : @ExternalFuns (PV_Join_PublicCaller.native base))
    (reached : Array aspis_core.field.QM31 28#usize → aspis_core.field.QM31 → Prop)
    (binding : P_NativePrefixBinding base ops reached) :
    ∀ p q, reached p q → Coeffs p ∧ Q q := by
  intro p q h
  obtain ⟨e,hp,hq⟩ := binding p q h
  rw [←hp,←hq]
  exact extracted_prefix_canonical base ops e
#print axioms extracted_prefix_canonical
#print axioms reached_canonical
end R1Z.PV_Canon
