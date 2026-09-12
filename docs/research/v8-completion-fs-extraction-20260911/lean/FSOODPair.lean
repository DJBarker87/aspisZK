import FSOODSampler
set_option autoImplicit false
namespace AspisV8Completion.FSOODPair
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSOODSampler
variable {Point : Type} [DecidableEq Point]
abbrev AnswerBytes := Fin (29*16) → UInt8

/-- No-hash response strategy for this deterministic slice. It receives the
first realised point, not the second point, queries or any future tape entry.
Use a script-valued response producer for adversaries that hash while building
these answers; this restricted producer is NOT such a general adversary. -/
def pair (decode : List Nat → Option Point) (answer : Point → AnswerBytes)
    (tape : Tape) (s : Transcript) : Except Error (Point × Point) × Transcript :=
  let first := circle decode tape 3 s
  match first.1 with
  | .error e => (.error e, first.2)
  | .ok point =>
      let bound := absorb tape first.2 62 (0 :: List.ofFn (answer point))
      let second := distinct decode point tape 3 bound
      (second.1.map (point, ·), second.2)

def pairScript (decode : List Nat → Option Point) (answer : Point → AnswerBytes)
    (digest : Block) : Script (List UInt8) Block (Except Error (Point × Point) × Block) 793 :=
  bind (circleScript decode 3 digest) fun first =>
    match first.1 with
    | .error e => .done (.error e, first.2)
    | .ok point => bind (absorbScript first.2 62 (0 :: List.ofFn (answer point))) fun bound =>
        map (fun second => (second.1.map (point, ·), second.2))
          (distinctScript decode point 3 bound)

theorem run_pair (decode : List Nat → Option Point) (answer : Point → AnswerBytes)
    (tape : Tape) (s : Transcript) :
    run tape (pairScript decode answer s.digest) s.oracle =
      (some ((pair decode answer tape s).1, (pair decode answer tape s).2.digest),
        (pair decode answer tape s).2.oracle) := by
  simp only [pairScript, run_bind, run_circle, pair]
  split
  · rfl
  · simp only [run_bind]
    rw [run_absorb tape (circle decode tape 3 s).2]
    simp only [run_map]
    rw [run_distinct]
    rfl

theorem pair_valid (decode : List Nat → Option Point) (answer : Point → AnswerBytes)
    (tape : Tape) (s : Transcript) (valid : FSFirstFresh.ValidHistory s.oracle) :
    FSFirstFresh.ValidHistory (pair decode answer tape s).2.oracle := by
  have h := FSFirstFresh.run_valid tape (pairScript decode answer s.digest) s.oracle valid
  simpa only [run_pair] using h

theorem pair_prefix (decode : List Nat → Option Point) (answer : Point → AnswerBytes)
    (tape : Tape) (s : Transcript) :
    Prefix s.oracle (pair decode answer tape s).2.oracle := by
  have h := FSOracleExecution.run_extends tape (pairScript decode answer s.digest) s.oracle
  simpa only [run_pair, Prefix] using h

theorem first_answer_size (answer : AnswerBytes) : (0 :: List.ofFn answer).length = 465 := by
  simp only [List.length_cons, List.length_ofFn]

/- The pair is sampled AFTER first-answer absorption. This is a chronological
same-state equality, not a product/uniform-pair law. In particular the second
sampler can hit the same cached squeeze input as an earlier sampler. Neither
the retry count nor the role labels imply independent random answers. The
second answer's absorption and the rest of the semantic proof are not here. -/
#print axioms run_pair
#print axioms pair_valid
#print axioms pair_prefix
end AspisV8Completion.FSOODPair
