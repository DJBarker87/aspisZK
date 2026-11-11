import R1JointContext
import AspisRows40Labels

/-! Aspis one-transaction verifier: the context parser of rows 33 to 39.

Given the absorb frame `c` that would start row `n` (33 ≤ n < 40) and the table
`T`, recover the prefix context: walk back from the absorbed state through
`n - 33` plain rows (each: advance edge, then the row's absorb frame; R1's
`DuplexSeek.seek` with fuel 2) to row 32's absorb frame, read the messages of
rows 33 .. n-1 at their indexed labels (`IndexedMessage.read`, canonical
encodings only), and parse row 32's context with R1's unchanged
`JointContext.parse` (semantic fuel 27, opening fuel 4, as in R1's row-32
component `UnifiedDecoder.component_rho`), requiring 31 records as R1 does.

No oracle is an input. This is the parser only: the completing component
(own reads, pending answers, output prefix) and its law are not constructed
here. -/
set_option autoImplicit false
noncomputable section
namespace AspisRows40.Context
open FS FS2 FS2.Duplex
open AspisR1
open AspisV8PairedCommitment
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
variable {M Cv : Type} {L : Nat}

structure Context (M : Type) (L : Nat) where
  /-- R1's row-32 context: 31 records, the query message, row 32's message. -/
  joint : JointContext.Context M L
  /-- Row 32's absorb frame. -/
  rhoAbsorb : Addr L
  /-- Rows 33 .. n-1: absorb frame and message, oldest first. -/
  tail : List (Addr L × M)
  /-- The state absorbed by row n's frame (the state after row n-1). -/
  endpoint : State
  /-- Row n's message. -/
  message : M

/-- Walk back `k` plain rows from the state `x`; return row 32's absorb frame
and the absorb frames of the `k` rows after it, oldest first. -/
def back (p : Params M Cv L) (T : Table (Addr L) State) : Nat → State → Option (Addr L × List (Addr L))
  | 0, x => (DuplexSeek.seek p T 2 x).map fun r => (r.1, [])
  | k + 1, x =>
      (DuplexSeek.seek p T 2 x).bind fun r =>
        (parseAbsorb r.1).bind fun parsed =>
          (back p T k parsed.1).map fun res => (res.1, res.2 ++ [r.1])

/-- Read the messages of consecutive rows starting at row `j`. -/
def readTail (p : Params M Cv L) : Nat → List (Addr L) → Option (List (Addr L × M))
  | _, [] => some []
  | j, a :: as =>
      (parseAbsorb a).bind fun parsed =>
        (IndexedMessage.read p j parsed.2.1 parsed.2.2).bind fun m =>
          (readTail p (j + 1) as).map fun rest => (a, m) :: rest

def parse (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte) (n : Nat)
    (c : Addr L) (T : Table (Addr L) State) : Option (Context M L) :=
  (parseAbsorb c).bind fun parsed =>
  (IndexedMessage.read p n parsed.2.1 parsed.2.2).bind fun m =>
  (back p T (n - 33) parsed.1).bind fun walked =>
  (readTail p 33 walked.2).bind fun tail =>
  (JointContext.parse p pubBytes tag 27 4 walked.1 T).bind fun ctx =>
  if ctx.records.length = 31 then some ⟨ctx, walked.1, tail, parsed.1, m⟩ else none

theorem back_length (p : Params M Cv L) (T : Table (Addr L) State) :
    ∀ (k : Nat) (x : State) (a32 : Addr L) (as : List (Addr L)),
      back p T k x = some (a32, as) → as.length = k := by
  intro k
  induction k with
  | zero =>
      intro x a32 as h
      cases hs : DuplexSeek.seek p T 2 x with
      | none => simp [back, hs] at h
      | some r =>
          simp only [back, hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
          rw [← h.2]; rfl
  | succ k ih =>
      intro x a32 as h
      cases hs : DuplexSeek.seek p T 2 x with
      | none => simp [back, hs] at h
      | some r =>
          cases hp : parseAbsorb r.1 with
          | none => simp [back, hs, hp] at h
          | some parsed =>
              cases hb : back p T k parsed.1 with
              | none => simp [back, hs, hp, hb] at h
              | some res =>
                  simp only [back, hs, hp, hb, Option.bind_some, Option.map_some,
                    Option.some.injEq, Prod.mk.injEq] at h
                  rw [← h.2, List.length_append, ih parsed.1 res.1 res.2 hb]
                  rfl

theorem readTail_length (p : Params M Cv L) :
    ∀ (as : List (Addr L)) (j : Nat) (out : List (Addr L × M)),
      readTail p j as = some out → out.length = as.length ∧ out.map Prod.fst = as := by
  intro as
  induction as with
  | nil =>
      intro j out h
      simp only [readTail, Option.some.injEq] at h
      subst h; simp
  | cons a as ih =>
      intro j out h
      cases hp : parseAbsorb a with
      | none => simp [readTail, hp] at h
      | some parsed =>
          cases hm : IndexedMessage.read p j parsed.2.1 parsed.2.2 with
          | none => simp [readTail, hp, hm] at h
          | some m =>
              cases hr : readTail p (j + 1) as with
              | none => simp [readTail, hp, hm, hr] at h
              | some rest =>
                  simp only [readTail, hp, hm, hr, Option.bind_some, Option.map_some,
                    Option.some.injEq] at h
                  subst h
                  obtain ⟨h1, h2⟩ := ih (j + 1) rest hr
                  simp [h1, h2]

/-- What a successful parse establishes: row n's label, 31 R1 records (so the
row-32 context is R1's), and `n - 33` tail rows. -/
theorem parse_sound (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte) (n : Nat)
    (c : Addr L) (T : Table (Addr L) State) (ctx : Context M L)
    (h : parse p pubBytes tag n c T = some ctx) :
    (∃ d, parseAbsorb c = some (ctx.endpoint, p.lbl n, d) ∧ p.enc ctx.message = d) ∧
    JointContext.parse p pubBytes tag 27 4 ctx.rhoAbsorb T = some ctx.joint ∧
    ctx.joint.records.length = 31 ∧
    ctx.tail.length = n - 33 := by
  unfold parse at h
  cases hc : parseAbsorb c with
  | none => simp [hc] at h
  | some parsed =>
      rcases parsed with ⟨x, l, d⟩
      simp only [hc, Option.bind_some] at h
      cases hm : IndexedMessage.read p n l d with
      | none => simp [hm] at h
      | some m =>
          simp only [hm, Option.bind_some] at h
          cases hb : back p T (n - 33) x with
          | none => simp [hb] at h
          | some walked =>
              rcases walked with ⟨a32, as⟩
              simp only [hb, Option.bind_some] at h
              cases ht : readTail p 33 as with
              | none => simp [ht] at h
              | some tail =>
                  simp only [ht, Option.bind_some] at h
                  cases hj : JointContext.parse p pubBytes tag 27 4 a32 T with
                  | none => simp [hj] at h
                  | some jc =>
                      simp only [hj, Option.bind_some] at h
                      by_cases hl : jc.records.length = 31
                      · rw [if_pos hl] at h
                        cases h
                        obtain ⟨hl1, hd, he⟩ := IndexedMessage.read_sound p n l d m hm
                        refine ⟨⟨d, by rw [hl1], he⟩, hj, hl, ?_⟩
                        rw [(readTail_length p as 33 tail ht).1]
                        exact back_length p T (n - 33) x a32 as hb
                      · rw [if_neg hl] at h
                        cases h

/-- Row 33, honest frames: if the table walk from the state after row 32 finds
row 32's honestly encoded absorb frame, and R1's row-32 parser succeeds there
with 31 records, the row-33 parser returns that context. -/
theorem parse_row33 (p : Params M Cv L) (pubBytes : Bytes) (tag : Byte)
    (T : Table (Addr L) State) (x : State) (m : M) (a32 : Addr L) (xs : List State)
    (jc : JointContext.Context M L)
    (hs : DuplexSeek.seek p T 2 x = some (a32, xs))
    (hj : JointContext.parse p pubBytes tag 27 4 a32 T = some jc)
    (hl : jc.records.length = 31) :
    parse p pubBytes tag 33 (absorbA p x (p.lbl 33) (p.enc m) (p.encLen m)) T =
      some ⟨jc, a32, [], x, m⟩ := by
  simp only [parse, parseAbsorb_absorbA, Option.bind_some, IndexedMessage.read_encoded,
    Nat.sub_self, back, hs, Option.map_some, readTail, hj, hl, if_true]

#print axioms back_length
#print axioms readTail_length
#print axioms parse_sound
#print axioms parse_row33

end AspisRows40.Context
end
