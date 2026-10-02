import AspisV8R19.R212SampledChordDomain
import AspisV8R19.R203ChordDataExecution

/-! Composition of computed chord-data and scalar inverse fragments after
completed encoded batches. Array construction/indexing and the selected
optimized batch-normalization inverse are separate obligations. -/
set_option autoImplicit false
namespace AspisV8R19.R213ComputedChordInverse
open Aeneas Aeneas.Std Result
open AspisR156FullFreeze.aspis_core
open AspisV8R15.ExactTowerBase
open DuplexFrames SourceDuplexStep
open R164ProductExecution (encode public_product)
open R165QuarticExecution (add)
noncomputable section
local instance : DecidableEq circle.SecureCirclePoint := Classical.decEq _

 def evalLine (d : R203ChordDataExecution.ChordData) (x y : field.QM31) :
    Result field.QM31 := do
  let bx ← field.QM31.mul d.abc.2.1 x
  let ax ← field.QM31.add d.abc.1 bx
  let cy ← field.QM31.mul d.abc.2.2 y
  field.QM31.add ax cy

 theorem evalLine_exact (p q : circle.SecureCirclePoint)
    (b0 b1 again : QM31Exact) (x y : CM31Exact) :
    evalLine (R203ChordDataExecution.exactData p q b0 b1 again)
      (encode (algebraMap CM31Exact QM31Exact x))
      (encode (algebraMap CM31Exact QM31Exact y)) =
      .ok (encode (R212SampledChordDomain.lineValue p q x y)) := by
  simp only [evalLine,R203ChordDataExecution.exactData,public_product,add,
    bind_tc_ok,R212SampledChordDomain.lineValue]

 def computedInverse (p q : circle.SecureCirclePoint)
    (b0 b1 again x y : field.QM31) :
    Result (core.result.Result field.QM31 AspisR156FullFreeze.Error) := do
  let r ← R203ChordDataExecution.rawData p q b0 b1 again
  match r with
  | .Err e => ok (.Err e)
  | .Ok d =>
    let line ← evalLine d x y
    let inv ← field.QM31.try_inv line
    AspisR156FullFreeze.core.option.Option.ok_or inv AspisR156FullFreeze.Error.Domain

 theorem sampled_computed_inverse (H : Bytes → State) (s0 s1 : State)
    (p q : circle.SecureCirclePoint) (t0 t1 : transcript.Transcript)
    (h0 : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s0) = .ok (.Ok p,t0))
    (h1 : transcript.Transcript.challenge_secure_circle_point
      (R167TranscriptPrimitiveExecution.transcriptFor H s1) = .ok (.Ok q,t1))
    (hne : core.cmp.PartialEq.ne.trait_default
      circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint p q = .ok true)
    (b0 b1 again : QM31Exact) (x y : CM31Exact) (hcircle : x^2+y^2=1) :
    computedInverse p q (encode b0) (encode b1) (encode again)
      (encode (algebraMap CM31Exact QM31Exact x))
      (encode (algebraMap CM31Exact QM31Exact y)) =
      .ok (.Ok (encode (R212SampledChordDomain.lineValue p q x y)⁻¹)) := by
  have hc0 := R178CircleOutputCanonical.successful_circle_canonical H s0 p t0 h0
  have hc1 := R178CircleOutputCanonical.successful_circle_canonical H s1 q t1 h1
  have hpq : p ≠ q := by
    have hcmp := R181SampledChordGuard.raw_secure_circle_point_ne p q
    rw [hne] at hcmp
    exact of_decide_eq_true (Result.ok.inj hcmp).symm
  have hd := R203ChordDataExecution.rawData_exact p q hc0.1 hc0.2 hc1.1 hc1.2 hpq
    b0 b1 again
  have hn := R212SampledChordDomain.sampled_line_nonzero H s0 s1 p q t0 t1
    h0 h1 hne x y hcircle
  simp only [computedInverse,hd,bind_tc_ok,evalLine_exact,
    R165QuarticExecution.try_inverse_nonzero _ hn,
    AspisR156FullFreeze.core.option.Option.ok_or]

#print axioms evalLine_exact
#print axioms sampled_computed_inverse
end
end AspisV8R19.R213ComputedChordInverse
