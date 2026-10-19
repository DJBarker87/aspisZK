import R1Z.Sem1UniformR1
import R1J.SamplerLawSpend
import ExtractedDigest32Begin
import ExtractedDigest32SamplerTransport

/-! (d) SemRows01 for a wire whose semantic rows are decoded by the spend path's extracted
sampler (LOG D65 follow-up, DESIGN-BUILD-INTEGRATION §10.3).  Joint module; no spend module is
changed.

* `decSpend ι a i`: the semantic-row decoder — row `i`'s oracle answer read by the extracted
  `qm31_sample` and the carrier `ι` (`= s1Spend ι (a i)`).
* `DecSpendRows W ι`: the wire's `sem 0` and `sem 1` are `decSpend` of rows 0 and 1.
* `semRows01_spend`: such a wire satisfies `SemRows01` with `s1 = s1Spend ι`.
* `row_refines`, `begin_refines_decSpend`: in the actual r1_wire `begin`, λ and χ are the
  extracted sampler applied to the squeeze blocks that `sample_block_validated` returns for
  rows 0 and 1 (from BeginCalls.begin_success, CallerStep.semantic_success and
  SamplerTransport.sample_toOld_success; nothing re-proved).
* `RSqueezeAnswer a i b`: the R-wire modelling choice, as ONE named premise — the privacy
  model's row-`i` oracle answer `a i` is the actual 32-byte squeeze block `b` of that row (the
  spend run computes it by Digest32 calls; the privacy games treat it as a random-oracle answer).
* `begin_agrees_dec`: under `DecSpendRows` and `RSqueezeAnswer` for rows 0 and 1, the actual
  `begin` outputs λ, χ equal the wire decoder's `sem 0`, `sem 1`. -/
set_option autoImplicit false
noncomputable section
namespace R1J.SemRowsSpend
open Aeneas Aeneas.Std Result
open R0Z.FsStatement R1Z.GamesR1 R1Z.Sem1UniformR1 R1J.SamplerLawSpend

variable {K CommitHandle Aux : Type} [Field K] [Fintype K] [DecidableEq K]
  [Algebra (ZMod AspisCircleGroupOrder.P) K]

/-- The semantic-row decoder. -/
def decSpend (ι : QF → K) (a : Fin 27 → OracleAnswer) (i : Fin 27) : K := s1Spend ι (a i)

/-- The wire decodes λ and χ from rows 0 and 1 by `decSpend`. -/
def DecSpendRows (W : R1Wire K CommitHandle Aux) (ι : QF → K) : Prop :=
  ∀ (a : Fin 27 → OracleAnswer) (o : Fin 4 → OracleAnswer) (qb : Fin 8 → OracleAnswer)
    (r : OracleAnswer),
    (W.dec a o qb r).sem 0 = decSpend ι a 0 ∧ (W.dec a o qb r).sem 1 = decSpend ι a 1

def semRows01_spend (W : R1Wire K CommitHandle Aux) (ι : QF → K) (hW : DecSpendRows W ι) :
    SemRows01 W where
  s1 := s1Spend ι
  sem1 a o qb r := (hW a o qb r).2
  sem0 a a' o qb r h := by
    rw [(hW a o qb r).1, (hW a' o qb r).1]
    exact congrArg (s1Spend ι) (h 0 (by decide))

theorem semRows01_spend_s1 (W : R1Wire K CommitHandle Aux) (ι : QF → K)
    (hW : DecSpendRows W ι) : (semRows01_spend W ι hW).s1 = s1Spend ι := rfl

/-- The R-wire modelling choice (named premise): the privacy model's row-`i` oracle answer is
the actual 32-byte squeeze block of that row. -/
def RSqueezeAnswer (a : Fin 27 → OracleAnswer) (i : Fin 27) (b : Array U8 32#usize) : Prop :=
  a i = arrEquiv.symm b

/-- A spend-path QM31 value read into K through the index carrier. -/
def toK (ι : QF → K) (q : aspis_core.field.QM31) : K :=
  ι (AspisR1.ExtractedCurrentQM31Exact.decode
    (AspisR1.ExtractedQM31SamplerCarrier.toCurrent
      (AspisR1PublicPreparation.SamplerTransport.toOld q)))

theorem row_refines (ι : QF → K) {H : Type} (D : aspis_core.Digest32 H)
    (t t' : r1_wire.SemanticTranscript H) (record : r1_wire.ValidatedRecord)
    (q : aspis_core.field.QM31)
    (h : r1_wire.SemanticTranscript.semantic_validated D t record = ok (.Ok q, t')) :
    ∃ block, r1_wire.SemanticTranscript.sample_block_validated D t record.row record.framed =
        ok (.Ok block, t') ∧ toK ι q = s1Spend ι (arrEquiv.symm block) := by
  obtain ⟨-, block, hb, hq⟩ := AspisR1PublicPreparation.CallerStep.semantic_success D t t' record q h
  refine ⟨block, hb, ?_⟩
  have hi := AspisR1PublicPreparation.SamplerTransport.sample_toOld_success block q hq
  have ha : arrEquiv (arrEquiv.symm block) = block := Equiv.apply_symm_apply _ _
  simp only [s1Spend, ha, hi, toK]

theorem begin_refines_decSpend (ι : QF → K) {H : Type} (D : aspis_core.Digest32 H)
    (pre : r1_wire.Prefix) (self after : r1_wire.SemanticTranscript H) (out : r1_wire.Challenges)
    (h : r1_wire.begin D pre self = ok (.Ok out, after)) :
    ∃ (t1 t2 : r1_wire.SemanticTranscript H) (r0 r1 : r1_wire.ValidatedRecord)
      (b0 b1 : Array U8 32#usize),
      r1_wire.Prefix.validated_record pre 0#u8 = ok (.Ok r0) ∧
      r1_wire.SemanticTranscript.sample_block_validated D self r0.row r0.framed = ok (.Ok b0, t1) ∧
      r1_wire.Prefix.validated_record pre 1#u8 = ok (.Ok r1) ∧
      r1_wire.SemanticTranscript.sample_block_validated D t1 r1.row r1.framed = ok (.Ok b1, t2) ∧
      toK ι out.lambda = s1Spend ι (arrEquiv.symm b0) ∧
      toK ι out.chi = s1Spend ι (arrEquiv.symm b1) := by
  obtain ⟨qs, hrun, hqs⟩ := AspisR1PublicPreparation.BeginCalls.begin_success D pre self after out h
  unfold AspisR1PublicPreparation.BeginCalls.rows at hrun
  cases hrun with
  | cons hr0 hs0 tail0 =>
    cases tail0 with
    | cons hr1 hs1 tail1 =>
      obtain ⟨b0, hb0, he0⟩ := row_refines ι D _ _ _ _ hs0
      obtain ⟨b1, hb1, he1⟩ := row_refines ι D _ _ _ _ hs1
      simp only [AspisR1PublicPreparation.BeginCalls.challengeList, List.cons.injEq] at hqs
      obtain ⟨rfl, rfl, -⟩ := hqs
      exact ⟨_, _, _, _, b0, b1, hr0, hb0, hr1, hb1, he0, he1⟩

/-- Under the wire decoder and the named R-wire premise for rows 0 and 1, the actual `begin`
outputs λ and χ are the wire's `sem 0` and `sem 1`. -/
theorem begin_agrees_dec (W : R1Wire K CommitHandle Aux) (ι : QF → K) (hW : DecSpendRows W ι)
    {H : Type} (D : aspis_core.Digest32 H) (pre : r1_wire.Prefix)
    (self after : r1_wire.SemanticTranscript H) (out : r1_wire.Challenges)
    (h : r1_wire.begin D pre self = ok (.Ok out, after)) :
    ∃ b0 b1 : Array U8 32#usize, ∀ (a : Fin 27 → OracleAnswer) (o : Fin 4 → OracleAnswer)
      (qb : Fin 8 → OracleAnswer) (r : OracleAnswer),
      RSqueezeAnswer a 0 b0 → RSqueezeAnswer a 1 b1 →
        toK ι out.lambda = (W.dec a o qb r).sem 0 ∧ toK ι out.chi = (W.dec a o qb r).sem 1 := by
  obtain ⟨_, _, _, _, b0, b1, -, -, -, -, he0, he1⟩ := begin_refines_decSpend ι D pre self after out h
  refine ⟨b0, b1, fun a o qb r h0 h1 => ?_⟩
  rw [(hW a o qb r).1, (hW a o qb r).2, decSpend, decSpend, h0, h1]
  exact ⟨he0, he1⟩

end R1J.SemRowsSpend

#print axioms R1J.SemRowsSpend.semRows01_spend
#print axioms R1J.SemRowsSpend.semRows01_spend_s1
#print axioms R1J.SemRowsSpend.row_refines
#print axioms R1J.SemRowsSpend.begin_refines_decSpend
#print axioms R1J.SemRowsSpend.begin_agrees_dec
