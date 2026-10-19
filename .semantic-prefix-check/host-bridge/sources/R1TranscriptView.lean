import R1JointNextLaw

/-! Pure representation of ordinary rounds, an initial prover message, and
the final query value. Dropping the first ordinary payload in this view is
justified only after connecting the actual fixed row-zero byte construction;
this module does not prove that connection. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.TranscriptView

inductive Message (M : Type)
  | initial (c1 : AspisV8R19.SourceDuplexStep.State)
  | payload (m : M)
  deriving DecidableEq, Repr

inductive Value (Cv : Type)
  | ordinary (v : Cv)
  | queries (result : Except Nat (List Nat))
  deriving DecidableEq, Repr

abbrev Challenge (Cv : Type) := Value Cv × AspisV8R19.SourceDuplexStep.State

def liftChallenge {Cv : Type} (ch : FS2.Duplex.Chal Cv) : Challenge Cv :=
  (.ordinary ch.1, ch.2)

def later {M Cv : Type} (rounds : List (M × FS2.Duplex.Chal Cv)) :
    List (Message M × Challenge Cv) :=
  rounds.map fun r => (Message.payload r.1, liftChallenge r.2)

def ordinary {M Cv : Type} (c1 : AspisV8R19.SourceDuplexStep.State) :
    List (M × FS2.Duplex.Chal Cv) → List (Message M × Challenge Cv)
  | [] => []
  | (_, ch) :: rs => (Message.initial c1, liftChallenge ch) :: later rs

def withQuery {M Cv : Type} (c1 : AspisV8R19.SourceDuplexStep.State)
    (rounds : List (M × FS2.Duplex.Chal Cv)) (qm : M)
    (qr : AspisV8R19.Q22SamplerProgram.Result) :
    List (Message M × Challenge Cv) :=
  ordinary c1 rounds ++
    [(Message.payload qm, (Value.queries qr.1, qr.2))]

theorem later_length {M Cv : Type} (rounds : List (M × FS2.Duplex.Chal Cv)) :
    (later rounds).length = rounds.length := by
  simp [later]

theorem ordinary_length {M Cv : Type} (c1 : AspisV8R19.SourceDuplexStep.State)
    (rounds : List (M × FS2.Duplex.Chal Cv)) :
    (ordinary c1 rounds).length = rounds.length := by
  cases rounds with
  | nil => rfl
  | cons r rs => simp [ordinary, later]

theorem withQuery_length {M Cv : Type} (c1 : AspisV8R19.SourceDuplexStep.State)
    (rounds : List (M × FS2.Duplex.Chal Cv)) (qm : M)
    (qr : AspisV8R19.Q22SamplerProgram.Result) :
    (withQuery c1 rounds qm qr).length = rounds.length + 1 := by
  simp [withQuery, ordinary_length]

theorem ordinary_cons {M Cv : Type} (c1 : AspisV8R19.SourceDuplexStep.State)
    (m : M) (ch : FS2.Duplex.Chal Cv) (rs : List (M × FS2.Duplex.Chal Cv)) :
    ordinary c1 ((m, ch) :: rs) =
      (Message.initial c1, liftChallenge ch) :: later rs := rfl

theorem ordinary_append {M Cv : Type} (c1 : AspisV8R19.SourceDuplexStep.State)
    (xs ys : List (M × FS2.Duplex.Chal Cv)) (hxs : xs ≠ []) :
    ordinary c1 (xs ++ ys) = ordinary c1 xs ++ later ys := by
  cases xs with
  | nil => contradiction
  | cons r rs =>
      cases r with
      | mk m ch =>
        simp [ordinary, later, List.map_append]

#print axioms later_length
#print axioms ordinary_length
#print axioms withQuery_length
#print axioms ordinary_cons
#print axioms ordinary_append

end AspisR1.TranscriptView
end
