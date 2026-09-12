import FSOODPair
set_option autoImplicit false
set_option Elab.async false
namespace AspisV8Completion.FSV8OODBodyScript
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSOODSampler
abbrev Bytes := List UInt8
variable {Point : Type} [DecidableEq Point]

def chunk (body : Bytes) (offset : Nat) : Fin 16 → UInt8 :=
  fun byte => body.getD (offset + byte.val) 0

/-- The two source OOD rows are fields 359..387 and 388..416.  Building the
byte record by concatenating the same sixteen-byte chunks makes the source
field order explicit and never exposes any later field to the answer builder. -/
def answerIndex (sample : Fin 2) (lane : Fin 29) : Fin 697 :=
  ⟨359 + 29*sample.val + lane.val, by omega⟩

def answerBytes (body : Bytes) (sample : Fin 2) : Bytes :=
  (List.ofFn fun lane : Fin 29 => List.ofFn (chunk body (16*(answerIndex sample lane).val))).flatten

set_option maxRecDepth 10000 in
theorem answer_bytes_size (body : Bytes) (sample : Fin 2) :
    (sample.val.toUInt8 :: answerBytes body sample).length = 1 + 29*16 := by
  simp [answerBytes]

/-- Literal little-endian M31 limb value used by the source field decoder. -/
def limbWord (bytes : Fin 16 → UInt8) (limb : Fin 4) : Nat :=
  (bytes ⟨4*limb.val, by omega⟩).toNat +
  256*(bytes ⟨4*limb.val+1, by omega⟩).toNat +
  65536*(bytes ⟨4*limb.val+2, by omega⟩).toNat +
  16777216*(bytes ⟨4*limb.val+3, by omega⟩).toNat

/-- This is precisely the parser-side canonicality condition for the 58
same-body OOD values; it asserts no property of later body fields. -/
def CanonicalOODFields (body : Bytes) : Prop :=
  ∀ sample : Fin 2, ∀ lane : Fin 29, ∀ limb : Fin 4,
    limbWord (chunk body (16*(answerIndex sample lane).val)) limb < 2147483647

instance (body : Bytes) : Decidable (CanonicalOODFields body) := by
  unfold CanonicalOODFields
  infer_instance

theorem answer_fields_canonical (body : Bytes) (canonical : CanonicalOODFields body)
    (sample : Fin 2) (lane : Fin 29) (limb : Fin 4) :
    limbWord (chunk body (16*(answerIndex sample lane).val)) limb < 2147483647 :=
  canonical sample lane limb

/-- A producer may make any bounded, adaptive hash calls while computing or
checking an answer.  Its only returned payload is then replaced by the exact
same-body canonical row.  An internal abort remains an abort with its consumed
cache/log/tape cursor; no future oracle answer is an input. -/
def answerScript {n : Nat} (work : Point → Script Bytes Block Unit n)
    (point : Point) (body : Bytes) (sample : Fin 2) :=
  map (fun _ => answerBytes body sample) (work point)

theorem run_answerScript {n : Nat} (work : Point → Script Bytes Block Unit n)
    (point : Point) (body : Bytes) (sample : Fin 2) (tape : Tape) (oracle : Oracle) :
    run tape (answerScript work point body sample) oracle =
      ((run tape (work point) oracle).1.map (fun _ => answerBytes body sample),
        (run tape (work point) oracle).2) :=
  run_map tape _ _ _

structure PairResult where
  first : Point
  second : Point
  afterFirstAnswer : Block
  afterSecondAnswer : Block

/-- Suffix after the second sampler.  Its error branch is statically padded,
but performs no dummy calls. -/
def afterSecond {m : Nat} (firstPoint : Point) (afterFirst : Block)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (secondDraw : Except Error Point × Block) :
    Script Bytes Block (Except Error (PairResult (Point := Point)) × Block) (1+m) :=
  match secondDraw.1 with
  | .error e => .done (n := 1+m) (Except.error e, secondDraw.2)
  | .ok secondPoint =>
      bind (answerScript (secondWork firstPoint) secondPoint body 1) fun secondAnswer =>
        bind (absorbScript secondDraw.2 62 (1 :: secondAnswer)) fun afterSecond =>
          .done (n := 0) ((Except.ok ⟨firstPoint, secondPoint,
            afterFirst, afterSecond⟩ :
              Except Error (PairResult (Point := Point))), afterSecond)

/-- Full source chronology: first V7 circle sampler; a bounded hash-capable
first-answer computation; literal label-62/sample-0/body-fields absorption;
the V7 three-candidate distinct sampler; a bounded hash-capable second-answer
computation; and literal sample-1/body-fields absorption. -/
def bodyPairScript {n m : Nat}
    (decode : List Nat → Option Point)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) :
    Script Bytes Block (Except Error (PairResult (Point := Point)) × Block)
      (((1+m)+594+1+n)+198) :=
  bind (circleScript decode 3 digest) fun firstDraw =>
    match firstDraw.1 with
    | .error e => .done (n := ((1+m)+594+1+n))
        ((Except.error e : Except Error (PairResult (Point := Point))), firstDraw.2)
    | .ok firstPoint =>
      bind (answerScript firstWork firstPoint body 0) fun firstAnswer =>
        bind (absorbScript firstDraw.2 62 (0 :: firstAnswer)) fun afterFirst =>
          bind (distinctScript decode firstPoint 3 afterFirst) fun secondDraw =>
            afterSecond firstPoint afterFirst secondWork body secondDraw

/-- The source parser has already made this check for all 697 fields.  Keeping
the consumed 58-field guard here makes canonicality intrinsic to this focused
slice: malformed OOD limbs abort before any OOD transcript call. -/
def checkedBodyPairScript {n m : Nat}
    (decode : List Nat → Option Point)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) :
    Script Bytes Block (Except Error (PairResult (Point := Point)) × Block)
      (((1+m)+594+1+n)+198) :=
  if CanonicalOODFields body then bodyPairScript decode firstWork secondWork body digest
  else .abort

theorem checked_success_canonical {n m : Nat}
    (decode : List Nat → Option Point)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle)
    (result : Except Error (PairResult (Point := Point)) × Block)
    (success : (run tape (checkedBodyPairScript decode firstWork secondWork body digest) oracle).1 =
      some result) : CanonicalOODFields body := by
  unfold checkedBodyPairScript at success
  split at success
  · assumption
  · contradiction

/-- Every call made by either answer builder and every retry/cached query is
in the one append-only execution log, including executions that abort. -/
theorem body_pair_prefix {n m : Nat}
    (decode : List Nat → Option Point)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle) :
    Prefix oracle (run tape (bodyPairScript decode firstWork secondWork body digest) oracle).2 := by
  simpa only [Prefix] using run_extends tape
    (bodyPairScript decode firstWork secondWork body digest) oracle

theorem body_pair_valid {n m : Nat}
    (decode : List Nat → Option Point)
    (firstWork : Point → Script Bytes Block Unit n)
    (secondWork : Point → Point → Script Bytes Block Unit m)
    (body : Bytes) (digest : Block) (tape : Tape) (oracle : Oracle)
    (valid : FSFirstFresh.ValidHistory oracle) :
    FSFirstFresh.ValidHistory
      (run tape (bodyPairScript decode firstWork secondWork body digest) oracle).2 :=
  FSFirstFresh.run_valid tape _ oracle valid

#print axioms answer_bytes_size
#print axioms answer_fields_canonical
#print axioms run_answerScript
#print axioms checked_success_canonical
#print axioms body_pair_prefix
#print axioms body_pair_valid
end AspisV8Completion.FSV8OODBodyScript
