import OraclePortHeader
import OraclePortChecks
import OracleDecisionMultiBuild

/-! Strict compact byte parser. No decoded fields or tree schedules are supplied
by a caller. The terminal message is a stored-proof byte carrier; the frozen
caller must separately prove that it supplies these bytes. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.OraclePortCompactDraft
open FS FS2
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open RawCutTranscriptRun (ErasedPrefix ErasedMessage)
attribute [local instance] Classical.propDecidable

def slice (b : Bytes) (offset n : Nat) : Bytes := (b.drop offset).take n

def little (b : Bytes) : Nat := b.foldr (fun x n => x.val + 256*n) 0

def le32 (n : Nat) : Bytes := (List.range 4).map (fun i => ⟨n / 256^i % 256, Nat.mod_lt _ (by decide)⟩)

def canonical (b : Bytes) : Prop :=
  b.length % 4 = 0 ∧ ∀ j ∈ List.range (b.length / 4), little (slice b (4*j) 4) < 2147483647

def expand (n : Nat) (b : Bytes) : Bytes :=
  ((List.range n).map (fun j => slice b (16*j) 16 ++ List.replicate 16 0)).flatten

def rowShape (row : Nat) : Nat × Nat :=
  if row = 2 then (1,32) else if row = 14 then (3,32)
  else if 15 ≤ row ∧ row ≤ 24 then (2,896)
  else if row = 25 then (4,3712) else if row = 26 then (5,928) else (0,0)

/-- Recursive on the row count, never on a concrete recurrence value. -/
def semanticRows : Nat → Nat → Bytes → Option (List Bytes)
  | 0, _, b => if b = [] then some [] else none
  | fuel+1, row, b => do
      let (tag, size) := rowShape row
      let stored := if 14 ≤ row then size / 2 else size
      if b.length < 5 + stored then none else do
        if b.take 5 ≠ (⟨tag % 256, Nat.mod_lt _ (by decide)⟩ :: le32 size) then none else do
          let payload := slice b 5 stored
          if 14 ≤ row ∧ ¬ canonical payload then none else do
            let logical := if 14 ≤ row then expand (size/32) payload else payload
            let tail ← semanticRows fuel (row+1) (b.drop (5+stored))
            pure ((b.take 5 ++ logical) :: tail)

structure Parsed where
  wire : Bytes
  semantic : List Bytes

/-- The compact opening's non-salt regions are all canonical M31 limbs.
This includes all four K fields and all eight C2 K fields. -/
def openingCanonical (q : Bytes) : Prop :=
  canonical (q.take 608) ∧ canonical (slice q 672 128)

def scan (b : Bytes) : Prop :=
  canonical (slice b 7031 464) ∧ canonical (slice b 7495 256) ∧
  canonical (slice b 7783 2272) ∧
  ∀ j ∈ List.range 22, openingCanonical (slice b (10055 + j*832) 832)

def parse (b : Bytes) : Option Parsed := do
  if OraclePortHeader.accepts b = false then none else do
    if ¬ scan b then none else do
      let rs ← semanticRows 27 0 (slice b 48 6983)
      pure ⟨b,rs⟩

def root0 (p : Parsed) : Bytes := slice p.wire 16 32
def root2 (p : Parsed) : Bytes := slice p.wire 7751 32

def framed (payload : Bytes) : Bytes := le32 payload.length ++ payload

/-- Message bytes through row 32. The root at row zero is handled separately. -/
def rowBytes (p : Parsed) (row : Nat) : Bytes :=
  if row < 27 then p.semantic[row]?.getD []
  else if row = 27 then framed (expand 29 (slice p.wire 7031 464))
  else if row = 28 then framed (slice p.wire 7495 32)
  else if row = 29 then framed (slice p.wire 7527 224)
  else if row = 30 then framed (slice p.wire 7751 256)
  else if row = 31 then framed (slice p.wire 8007 2048)
  else framed []

def Aligned (p : Parsed) (tr : ErasedPrefix) : Prop :=
  tr.statement.tag = (p.wire[8]?.getD 0) ∧
  (∃ decoded, SemanticPublicWire.parsePublic tr.statement.pubBytes = some decoded) ∧
  tr.rounds.length = 33 ∧
  (∃ root c, tr.rounds[0]? = some (.initial root,c) ∧ bytes root = root0 p) ∧
  ∀ row, 0 < row → row < 33 → ∃ b c,
    tr.rounds[row]? = some (.payload b,c) ∧ b.val = rowBytes p row

/-- The parser reads the whole stored compact proof from the erased terminal
payload. No separate proof argument can disagree with the reached message. -/
def terminalBytes : ErasedMessage → Bytes
  | .initial _ => []
  | .payload b => b.val

def parseTerminal (tr : ErasedPrefix) (m : ErasedMessage) : Option Parsed := do
  let p ← parse (terminalBytes m)
  if Aligned p tr then some p else none

theorem parse_header (b : Bytes) (p : Parsed) (h : parse b = some p) :
    OraclePortHeader.accepts b = true ∧ p.wire = b := by
  unfold parse at h
  split at h
  · contradiction
  · rename_i hh
    have hb : OraclePortHeader.accepts b = true := Bool.eq_true_of_not_eq_false hh
    split at h
    · contradiction
    · cases hs : semanticRows 27 0 (slice b 48 6983) <;> simp [hs] at h
      subst p
      exact ⟨hb,rfl⟩

theorem terminal_alignment (tr : ErasedPrefix) (m : ErasedMessage) (p : Parsed)
    (h : parseTerminal tr m = some p) :
    parse (terminalBytes m) = some p ∧ p.wire = terminalBytes m ∧ Aligned p tr := by
  unfold parseTerminal at h
  cases hp : parse (terminalBytes m) with
  | none => simp [hp] at h
  | some p' =>
    by_cases ha : Aligned p' tr
    · simp [hp, ha] at h
      subst p
      exact ⟨hp, (parse_header _ _ hp).2, ha⟩
    · simp [hp, ha] at h

theorem physical_tag (tr : ErasedPrefix) (m : ErasedMessage) (p : Parsed)
    (h : parseTerminal tr m = some p) :
    tr.statement.tag = 2 ∧ (terminalBytes m)[8]? = some 2 := by
  obtain ⟨hp,same,aligned⟩ := terminal_alignment tr m p h
  have ht := ((OraclePortHeader.accepts_iff _).mp (parse_header _ _ hp).1).2.2.1
  refine ⟨?_,ht⟩
  have ha := aligned.1
  simpa only [same, ht, Option.getD_some] using ha

#print axioms parse_header
#print axioms terminal_alignment
#print axioms physical_tag
end AspisR1.OraclePortCompactDraft
end
