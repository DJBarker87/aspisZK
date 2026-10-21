import OraclePortStoredParserC4
import OraclePortStoredChecksC4

/-! Byte-derived arithmetic candidate for the stored-proof port. Every word
slot is decoded from an opening selected by reached queries; no external
word/source parameter is accepted. Identification with compiler cut-recovered
words and frozen execution is still required before calling this completed dV. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortStoredDecisionDraftC4
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open OraclePortCompactDraft OraclePortSelectedDraft OraclePortBatchDraft
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
open RecordedBinaryExperimentBin (SourceInputs)
attribute [local instance] Classical.propDecidable

/-- Global first occurrence, including a query repeated across TX batches. -/
def selectedPosition (q : Fin 22 → Fin 262144) (kind leafIndex : Nat) : Option Nat :=
  (List.range 22).find? (fun pos => decide (index q kind pos = leafIndex))

def packed (p : Parsed) (q : Fin 22 → Fin 262144) (kind i : Nat) : Option Bytes :=
  (selectedPosition q kind i).map fun pos =>
    let b := opening p pos
    if kind = 0 then b.take 480 else if kind = 1 then slice b 480 128 else slice b 672 128

def words (p : Parsed) (q : Fin 22 → Fin 262144) : CanonicalCutEnrichedTranscript.Words :=
  CanonicalCutEnrichedTranscript.wordsFromMaps
    (fun i => packed p q 0 i.val) (fun i => packed p q 1 i.val)
    (fun i => packed p q 2 i.val)

def restore (w : CanonicalCutEnrichedTranscript.Words) (row : Nat) :
    ErasedMessage → LiteralTranscript.Message
  | .initial root => .initial root w.c1
  | .payload b => if row = 2 then .c2 b w.c2
      else if row = 30 then .second b w.final else .payload b

def typedRows (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix) :
    LiteralAcceptanceTerminal.TranscriptRounds :=
  tr.rounds.mapIdx fun row mc => (restore (words p q) row mc.1,mc.2)

def input (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix) : Option SourceInputs :=
  if h : ∃ i, D0InstanceAdmission.Fields tr i then
    (LiteralMatchingData.read (typedRows p q tr)).map
      (fun data => OraclePortDataChoiceDraft.withData (Classical.choose h) data)
  else none

def arithmetic (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix) : Bool :=
  match input p q tr with
  | none => false
  | some i => D0TypedChecks.verify (typedRows p q tr) i

/-- A fully specified candidate, including typed semantic, pairing,
first-match and accumulator checks. Physical checkpoint hashing and the
selected-to-cut-word transfer are not hidden in the definition. -/
def decision : OraclePortStoredExperimentC4.Decision := fun stored tr _ =>
  if OraclePortAdmission.Guard tr then
    match OraclePortStoredParserC4.parseReached stored tr,queries tr with
    | some p,some q => if Padding p q then
        bind (verifySlots p q slots) fun merkle => .done (merkle && arithmetic p q tr)
      else .done false
    | _,_ => .done false
  else .done false

theorem restore_erases (w : CanonicalCutEnrichedTranscript.Words) (row : Nat)
    (m : ErasedMessage) : LiteralTranscript.erase (restore w row m) = m := by
  cases m with
  | initial root => rfl
  | payload b => by_cases h2 : row = 2 <;> by_cases h30 : row = 30 <;>
      simp only [restore,h2,h30,↓reduceIte,LiteralTranscript.erase]

theorem input_fields (p : Parsed) (q : Fin 22 → Fin 262144) (tr : ErasedPrefix)
    (i : SourceInputs) (h : input p q tr = some i) :
    D0InstanceAdmission.Fields tr i ∧ LiteralMatchingData.read (typedRows p q tr) = some i.data := by
  unfold input at h
  split at h
  · rename_i existsFields
    cases read : LiteralMatchingData.read (typedRows p q tr) with
    | none => simp only [read,Option.map_none,reduceCtorEq] at h
    | some data =>
      simp only [read,Option.map_some,Option.some.injEq] at h
      subst i
      exact ⟨Classical.choose_spec existsFields,read⟩
  · contradiction

theorem decision_budget : OraclePortStoredExperimentC4.Budget decision := by
  intro stored H tr m
  unfold decision
  split
  · split
    · split
      · have bound := OraclePortSixSlotBudgetC3.batch_budget H _ _ (by assumption)
        simpa only [eval_bind,eval,List.append_nil] using bound.trans (by decide)
      · simp only [eval,List.length_nil]; omega
    · simp only [eval,List.length_nil]; omega
  · simp only [eval,List.length_nil]; omega

theorem accepted (stored : Bytes) (tr : ErasedPrefix) (m : ErasedMessage)
    (H : Bytes → State) (ha : (eval H (decision stored tr m)).2 = true) :
    OraclePortAdmission.Guard tr ∧ ∃ p q i,
      OraclePortStoredParserC4.parseReached stored tr = some p ∧
      queries tr = some q ∧ Padding p q ∧
      (eval H (verifySlots p q slots)).2 = true ∧ input p q tr = some i ∧
      D0TypedChecks.verify (typedRows p q tr) i = true := by
  by_cases guard : OraclePortAdmission.Guard tr
  · refine ⟨guard,?_⟩
    cases hp : OraclePortStoredParserC4.parseReached stored tr with
    | none => simp only [decision,if_pos guard,hp,eval,Bool.false_eq_true] at ha
    | some p =>
      cases hq : queries tr with
      | none => simp only [decision,if_pos guard,hp,hq,eval,Bool.false_eq_true] at ha
      | some q =>
        by_cases pad : Padding p q
        · have both : (eval H (verifySlots p q slots)).2 = true ∧ arithmetic p q tr = true := by
            simpa only [decision,if_pos guard,hp,hq,if_pos pad,eval_bind,eval,Bool.and_eq_true] using ha
          cases hi : input p q tr with
          | none => simp only [arithmetic,hi,Bool.false_eq_true] at both
          | some i =>
            exact ⟨p,q,i,rfl,rfl,pad,both.1,hi,by simpa only [arithmetic,hi] using both.2⟩
        · simp only [decision,if_pos guard,hp,hq,if_neg pad,eval,Bool.false_eq_true] at ha
  · simp only [decision,if_neg guard,eval,Bool.false_eq_true] at ha

#print axioms restore_erases
#print axioms input_fields
#print axioms decision_budget
#print axioms accepted
end AspisR1.OraclePortStoredDecisionDraftC4
end
