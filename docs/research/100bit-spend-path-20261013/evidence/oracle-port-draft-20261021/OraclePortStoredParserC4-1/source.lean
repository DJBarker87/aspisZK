import OraclePortStoredExperimentC4
import OraclePortSixSlotBudgetC3

/-! Parse the actual separate stored-proof argument, then compare its absorbed
projection with reached rows. This repairs the terminal size error; the
multiproof kernel is still only one component of the complete verifier. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredParserC4
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open RawCutTranscriptRun (ErasedPrefix)
attribute [local instance] Classical.propDecidable

def parseReached (stored : Bytes) (tr : ErasedPrefix) : Option Parsed := do
  let p ← parse stored
  if Aligned p tr then some p else none

theorem parsed (stored : Bytes) (tr : ErasedPrefix) (p : Parsed)
    (h : parseReached stored tr = some p) :
    parse stored = some p ∧ p.wire = stored ∧ Aligned p tr := by
  unfold parseReached at h
  cases hp : parse stored with
  | none => simp only [hp,Option.bind_none,reduceCtorEq] at h
  | some p' =>
    by_cases ha : Aligned p' tr
    · simp only [hp,Option.bind_some,if_pos ha,Option.some.injEq] at h
      subst p
      exact ⟨hp,(parse_header _ _ hp).2,ha⟩
    · simp only [hp,Option.bind_some,if_neg ha,reduceCtorEq] at h

theorem parse_of_parts (stored : Bytes) (semantic : List Bytes) (tr : ErasedPrefix)
    (header : OraclePortHeader.accepts stored = true) (canonical : scan stored)
    (rows : semanticRows 27 0 (slice stored 48 6983) = some semantic)
    (aligned : Aligned ⟨stored,semantic⟩ tr) :
    parseReached stored tr = some ⟨stored,semantic⟩ := by
  simp only [parseReached,parse,header,Bool.true_eq_false,↓reduceIte,
    canonical,not_true_eq_false,rows,Option.bind_some,aligned]

def kernel : OraclePortStoredExperimentC4.Decision := fun stored tr _ =>
  match parseReached stored tr, queries tr with
  | some p, some q => if Padding p q then verifySlots p q slots else .done false
  | _, _ => .done false

theorem kernel_budget : OraclePortStoredExperimentC4.Budget kernel := by
  intro stored H tr m
  unfold kernel
  split
  · split
    · exact (OraclePortSixSlotBudgetC3.batch_budget H _ _ (by assumption)).trans (by decide)
    · simp only [eval,List.length_nil]; omega
  · simp only [eval,List.length_nil]; omega

/-- Accepted kernels now expose real stored bytes, instead of a contradiction
with the sampler-message bound. Arithmetic acceptance is not concluded. -/
theorem kernel_accepted (H : Bytes → State) (stored : Bytes)
    (tr : ErasedPrefix) (m : RawCutTranscriptRun.ErasedMessage)
    (ha : (eval H (kernel stored tr m)).2 = true) :
    ∃ p q, parseReached stored tr = some p ∧ queries tr = some q ∧
      Padding p q ∧ (eval H (verifySlots p q slots)).2 = true := by
  cases hp : parseReached stored tr with
  | none => simp only [kernel,hp,eval,Bool.false_eq_true] at ha
  | some p =>
    cases hq : queries tr with
    | none => simp only [kernel,hp,hq,eval,Bool.false_eq_true] at ha
    | some q =>
      by_cases hpad : Padding p q
      · exact ⟨p,q,hp,hq,hpad,by simpa only [kernel,hp,hq,if_pos hpad] using ha⟩
      · simp only [kernel,hp,hq,if_neg hpad,eval,Bool.false_eq_true] at ha

#print axioms parsed
#print axioms parse_of_parts
#print axioms kernel_budget
#print axioms kernel_accepted
end AspisR1.OraclePortStoredParserC4
end
