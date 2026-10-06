import FS2.Duplex

/-! # The duplex decoder and its chain density

`decode a T`: parse `a` as an absorb address `bytes s ++ [0, label] ++ data`;
walk the table back from `s` to the initial state (unique `advance` cell with
output `s`, unique `absorb` cell with output the advanced-from state, and so
on), recovering each round's message and absorbed state; the completing
sampler reads `a`, then the new `squeeze`/`advance` cells together with every
earlier `squeeze` cell still missing from `T`, and outputs the completed
prefix, the message and the new challenge.

`chainDensity`: from (D2′).  The completing sampler's law is the law of the
round's own cells averaged over the late cells; permuting the multi-cell law
puts the late cells outside, where (D2′) applies to each fixed completion. -/
set_option autoImplicit false
namespace FS2.Duplex

open FS FS2 AspisV8R19.MemoizedProgramLaw AspisV8R19.OracleProgramOps
open AspisV8R19.OracleResampling AspisV8R19.CausalFirstHitUnionBound
open AspisV8PairedCommitment AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open scoped BigOperators
noncomputable section

variable {M Cv : Type} {L : Nat}

/-! ## Parsing absorb addresses -/

def stateOfBytes (b : Bytes) : State := fun j => b.getD j.val 0

def parseAbsorb (a : Addr L) : Option (State × Byte × Bytes) :=
  let b := a.toBytes
  if 34 ≤ b.length ∧ b.getD 32 1 = 0 then some (stateOfBytes b, b.getD 33 0, b.drop 34) else none

theorem stateOfBytes_bytes (s : State) (tail : Bytes) : stateOfBytes (bytes s ++ tail) = s := by
  funext j
  simp only [stateOfBytes, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by rw [bytes_length]; exact j.isLt)]
  rw [bytes, List.getElem?_ofFn, dif_pos j.isLt]
  rfl

theorem absorb_getD32 (s : State) (l : Byte) (data : Bytes) :
    (bytes s ++ [0, l] ++ data).getD 32 1 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [bytes_length]),
    List.getElem?_append_right (by rw [bytes_length]), bytes_length]
  rfl

theorem absorb_getD33 (s : State) (l : Byte) (data : Bytes) :
    (bytes s ++ [0, l] ++ data).getD 33 0 = l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by simp [bytes_length]),
    List.getElem?_append_right (by rw [bytes_length]; omega), bytes_length]
  rfl

theorem absorb_drop34 (s : State) (l : Byte) (data : Bytes) :
    (bytes s ++ [0, l] ++ data).drop 34 = data := by
  rw [List.drop_append_of_le_length (by simp [bytes_length])]
  rw [List.drop_eq_nil_of_le (by simp [bytes_length])]
  rfl

theorem parseAbsorb_absorbA (p : Params M Cv L) (s : State) (l : Byte) (data : Bytes)
    (h : data.length ≤ p.D) : parseAbsorb (absorbA p s l data h) = some (s, l, data) := by
  simp only [parseAbsorb, absorbA, Addr.toBytes_ofBytes, absorb]
  have hlen : (bytes s ++ [0, l] ++ data).length = 34 + data.length := by
    simp [bytes_length]; omega
  rw [if_pos ⟨by omega, absorb_getD32 s l data⟩]
  rw [List.append_assoc, stateOfBytes_bytes, ← List.append_assoc, absorb_getD33, absorb_drop34]

/-! ## Unique elements and the table walk -/

def theUnique {α : Type} (s : Finset α) : Option α := by
  classical exact if h : ∃ a, s = {a} then some (Classical.choose h) else none

theorem theUnique_eq_some {α : Type} (s : Finset α) (a : α) :
    theUnique s = some a ↔ s = {a} := by
  classical
  unfold theUnique
  constructor
  · intro h
    split_ifs at h with hex
    obtain rfl := Option.some.inj h
    exact Classical.choose_spec hex
  · intro h
    have hex : ∃ b, s = {b} := ⟨a, h⟩
    rw [dif_pos hex]
    congr 1
    have := Classical.choose_spec hex
    exact (Finset.singleton_inj.mp (h.symm.trans this)).symm

/-- States whose `advance` cell outputs `s`. -/
def advPre (p : Params M Cv L) (T : Table (Addr L) State) (s : State) : Finset State := by
  classical exact Finset.univ.filter fun s' => T (advanceA p s') = some s

/-- Absorb addresses whose cell outputs `s'`. -/
def absCells (T : Table (Addr L) State) (s' : State) : Finset (Addr L) := by
  classical exact Finset.univ.filter fun a => T a = some s' ∧ (parseAbsorb a).isSome

/-- One round record: absorbed-from state, absorbed state, message, next state. -/
abbrev Rec (M : Type) := State × State × M × State

/-- Walk the table back from state `s` to the initial state. -/
def walk (p : Params M Cv L) (T : Table (Addr L) State) : Nat → State → Option (List (Rec M))
  | 0, s => if s = p.iv then some [] else none
  | n + 1, s =>
      if s = p.iv then some [] else
      match theUnique (advPre p T s) with
      | none => none
      | some s' =>
        match theUnique (absCells T s') with
        | none => none
        | some a =>
          match parseAbsorb a with
          | none => none
          | some (sp, _, data) =>
            match p.dec data with
            | none => none
            | some m => (walk p T n sp).map (· ++ [(sp, s', m, s)])

/-! ## The completing sampler -/

/-- The rounds completed from the records (from round index `j`), reading
each round's squeeze value from the table when present and from the sampler's
answers otherwise. -/
def completeRounds (p : Params M Cv L) (T : Table (Addr L) State) (acc : Addr L → State) :
    Nat → List (Rec M) → List (M × Chal Cv)
  | _, [] => []
  | j, r :: rs =>
      (r.2.2.1, (p.σ j ((T (squeezeA p r.2.1)).getD (acc (squeezeA p r.2.1))), r.2.2.2)) ::
        completeRounds p T acc (j + 1) rs

def completePrefix {X : Type} (p : Params M Cv L) (x : X) (T : Table (Addr L) State)
    (recs : List (Rec M)) (acc : Addr L → State) : Prefix X M (Chal Cv) :=
  ⟨x, completeRounds p T acc 0 recs⟩

theorem completeRounds_length (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) : ∀ (j : Nat) (recs : List (Rec M)),
    (completeRounds p T acc j recs).length = recs.length := by
  intro j recs
  induction recs generalizing j with
  | nil => rfl
  | cons r rs ih => simp [completeRounds, ih]

theorem completeRounds_update (p : Params M Cv L) (T : Table (Addr L) State)
    (acc : Addr L → State) (c : Addr L) (v : State) :
    ∀ (j : Nat) (recs : List (Rec M)), (∀ r ∈ recs, squeezeA p r.2.1 ≠ c) →
      completeRounds p T (Function.update acc c v) j recs = completeRounds p T acc j recs := by
  intro j recs
  induction recs generalizing j with
  | nil => intro _; rfl
  | cons r rs ih =>
      intro h
      simp only [completeRounds]
      rw [Function.update_of_ne (h r (List.mem_cons_self ..)),
        ih (j + 1) (fun r' hr' => h r' (List.mem_cons_of_mem _ hr'))]

theorem completePrefix_round {X : Type} (p : Params M Cv L) (x : X) (T : Table (Addr L) State)
    (recs : List (Rec M)) (acc : Addr L → State) :
    (completePrefix p x T recs acc).round = recs.length := by
  simp [completePrefix, Prefix.round, completeRounds_length]

/-- Earlier squeeze cells still missing from the table, other than the new
round's two cells. -/
def missingCells (p : Params M Cv L) (T : Table (Addr L) State) (recs : List (Rec M))
    (s' : State) : List (Addr L) :=
  ((recs.map fun r => squeezeA p r.2.1).filter fun c =>
    T c = none ∧ c ≠ squeezeA p s' ∧ c ≠ advanceA p s').dedup

theorem missingCells_nodup (p : Params M Cv L) (T : Table (Addr L) State) (recs : List (Rec M))
    (s' : State) :
    (squeezeA p s' :: advanceA p s' :: missingCells p T recs s').Nodup := by
  refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, List.nodup_dedup _⟩⟩
  · simp only [List.mem_cons, not_or]
    refine ⟨squeezeA_ne_advanceA p s', ?_⟩
    intro h
    rw [missingCells, List.mem_dedup, List.mem_filter] at h
    exact (decide_eq_true_iff.mp h.2).2.1 rfl
  · intro h
    rw [missingCells, List.mem_dedup, List.mem_filter] at h
    exact (decide_eq_true_iff.mp h.2).2.2 rfl

/-- The freshly absorbed state repeats an earlier absorbed state (a collision
configuration; the decoder then outputs a never-counted round-`r` dummy). -/
def collides (recs : List (Rec M)) (s' : State) : Prop := s' ∈ recs.map fun r => r.2.1

instance (recs : List (Rec M)) (s' : State) : Decidable (collides recs s') :=
  inferInstanceAs (Decidable (s' ∈ recs.map fun r => r.2.1))

def decode {X : Type} (p : Params M Cv L) (x : X) (a : Addr L) (T : Table (Addr L) State) :
    Option (Sampler (Addr L) State (Prefix X M (Chal Cv) × M × Chal Cv)) :=
  match parseAbsorb a with
  | none => none
  | some (s, _, data) =>
    match p.dec data, walk p T p.rounds s with
    | some m, some recs =>
        some (.ask a fun s' =>
          if collides recs s' then
            .done (⟨x, List.replicate p.rounds (m, (p.σ 0 s', s'))⟩, m, (p.σ 0 s', s'))
          else
          .multi (squeezeA p s') (advanceA p s' :: missingCells p T recs s')
            (missingCells_nodup p T recs s') fun acc =>
              .done (completePrefix p x T recs acc, m,
                (p.σ recs.length (acc (squeezeA p s')), acc (advanceA p s'))))
    | _, _ => none

/-- The duplex protocol object (for a fixed statement `x`). -/
def protocol {X W Pf : Type} (p : Params M Cv L) (x : X) (msg : Pf → Nat → M)
    (extract : X → Table (Addr L) State → Option W) :
    FS2.Protocol X M (Chal Cv) W Pf (Addr L) State where
  r := p.rounds
  msg := msg
  samp := samp p
  decode := decode p x
  extract := extract

end
end FS2.Duplex
