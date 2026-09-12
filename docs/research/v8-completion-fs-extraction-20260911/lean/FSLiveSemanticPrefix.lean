import FSNonzeroQM31
import SameBodySemanticWire
import SameBodyAuthenticatedIncrement
import SemanticWireExecution

/-!
# Live selected semantic transcript prefix

This is the source-shaped transcript prefix of
`performance_verifier::semantic`.  It starts from `Transcript::new`, absorbs
the optional positive-transfer profile record, then the V8 profile, statement,
C1 root, C2 root, literal state-only registry/helper records and masked-claim
record.  Every field challenge uses the live bounded sampler.  The ten compact
semantic messages are literal body slices and precede their respective `z`
draws.

The public statement binding and compile-time profile choice remain explicit
inputs.  The roots and fixed fields are parsed from the body itself.  This file
stops after constructing the carried semantic scalar: it does not assume or
model semantic-terminal acceptance.
-/

set_option autoImplicit false
set_option Elab.async false

namespace AspisV8Completion.FSLiveSemanticPrefix

open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSNonzeroQM31
open AspisV5ComponentCQM31TowerExact
open AspisV8.SameBodySequentialCodec
open AspisV8Completion.SameBodySemanticWire
open AspisV8Completion.SemanticWireExecution
open AspisV8Completion.SameBodyAuthenticatedIncrement

abbrev Bytes := List UInt8
abbrev K := QM31Exact
abbrev Binding := Fin 32 -> UInt8

noncomputable section

def zeroDigest : Block := fun _ => 0

def selectedProfile : Bytes :=
  [65,86,56,47,112,97,121,109,101,110,116,45,101,120,116,114,97,99,116,
   105,111,110,47,118,49]

/-- Exact verifier-derived 107-byte adapter of the selected
`v8_positive_transfer` build: fixed profile text, V8 profile binding,
row/column/lane, old/new mask-inventory fingerprints, and count 3802. -/
def selectedPositiveDescriptor : Bytes :=
  [65,86,56,47,112,111,115,105,116,105,118,101,45,116,114,97,110,115,102,
   101,114,47,97,99,116,105,118,101,45,99,101,108,108,45,111,118,101,114,
   119,114,105,116,101,47,108,97,110,101,57,52,47,118,49,
   121,147,51,56,96,194,205,16,170,24,62,117,31,39,16,186,39,155,51,42,
   187,191,221,206,119,59,50,23,103,240,1,186,
   246,3,3,94,209,133,66,79,213,243,218,249,137,113,108,165,69,18,102,
   107,218,14]

/-- Literal 28-byte `STATE_ONLY_CONSTRAINT_REGISTRY_BYTES` record. -/
def constraintRegistry : Bytes :=
  [1,29,95,0,10,27,28,102,0,17,
   48,33,175,20,236,180,29,18,
   251,234,229,239,81,34,103,18,0,0]

def helperZero : Bytes := List.replicate 16 0

def maskClaimRecord (claim : K) : Bytes := [27,10] ++ canonicalBytes claim

def semanticRoundBytes (body : Bytes) (round : Nat) : Bytes :=
  UInt8.ofNat round :: (body.drop ((1 + 27 * round) * 16)).take (27 * 16)

def exactArithmetic : Arithmetic K where
  zero := 0
  add := fun a b => a+b
  sub := fun a b => a-b
  mul := fun a b => a*b
  square := fun x => x*x
  sumProducts3 := fun a b => (List.finRange 3).foldl (fun s i => s + a i*b i) 0

def wordOfValues (values : List K) : Word K := fun i => values.getD i.val 0

inductive Error where
  | badBody
  | lambda (error : FSNonzeroQM31.Error)
  | chi (error : FSNonzeroQM31.Error)
  | batching (draw : Nat) (error : FSNonzeroQM31.Error)
  | eta (error : FSNonzeroQM31.Error)
  | semanticRound (round : Nat) (error : FSNonzeroQM31.Error)
  deriving DecidableEq, Repr

structure Batching where
  theta : K
  zc : Fin 10 -> K
  mu : K

structure Success where
  lambda : K
  chi : K
  theta : K
  zc : Fin 10 -> K
  mu : K
  eta : K
  z : Fin 10 -> K
  finalClaim : K
  finalDigest : Block

abbrev Result := Except Error Success

/-- A compile-time-one-call optional absorb.  `none` performs no dummy hash
call; `some bytes` is the selected positive-transfer profile adapter. -/
def optionalProfileScript (positiveTransfer : Bool) (digest : Block) :
    Script Bytes Block Block 1 :=
  if positiveTransfer then absorbScript digest 1 selectedPositiveDescriptor
  else pad (.done digest) 1

def indexedCandidates : (count index : Nat) -> Block ->
    Script Bytes Block (Except (Nat × FSNonzeroQM31.Error) (List K) × Block)
      (66 * count)
  | 0, _, digest => .done (.ok [], digest)
  | count+1, index, digest =>
      bind (candidateScript digest) fun draw =>
        match draw.1 with
        | .error e => .done (Except.error (index,e), draw.2)
        | .ok value =>
          FSTranscriptScript.map (fun rest => match rest.1 with
            | .error e => (Except.error e, rest.2)
            | .ok values => (Except.ok (value::values), rest.2))
            (indexedCandidates count (index+1) draw.2)

def batchingOfList (values : List K) : Batching :=
  { theta := values.getD 0 0
    zc := fun i => values.getD (i.val+1) 0
    mu := values.getD 11 0 }

structure RoundState where
  z : List K
  claim : K
  digest : Block

def roundBudget : Nat -> Nat
  | 0 => 0
  | n+1 => roundBudget n + 66 + 1

def semanticRounds (body : Bytes) (values : List K) :
    (remaining round : Nat) -> K -> Block ->
      Script Bytes Block (Except (Nat × FSNonzeroQM31.Error) RoundState)
        (roundBudget remaining)
  | 0, _, claim, digest => .done (.ok ⟨[],claim,digest⟩)
  | remaining+1, round, claim, digest =>
      bind (m := roundBudget remaining + 66)
          (absorbScript digest 48 (semanticRoundBytes body round)) fun afterMessage =>
        bind (m := roundBudget remaining) (candidateScript afterMessage) fun draw =>
          match draw.1 with
          | .error e => .done (Except.error (round,e))
          | .ok alpha =>
            let nextClaim := evaluate exactArithmetic
              (polynomial exactArithmetic claim
                (sent (wordOfValues values) ⟨round % 10, Nat.mod_lt _ (by decide)⟩)) alpha
            FSTranscriptScript.map (fun rest => match rest with
              | .error e => Except.error e
              | .ok state => Except.ok
                  (RoundState.mk (alpha::state.z) state.claim state.digest))
              (semanticRounds body values remaining (round+1) nextClaim draw.2)

def tenCoordinates (values : List K) : Fin 10 -> K :=
  fun i => values.getD i.val 0

/-- Exact chronological prefix.  The Boolean selects the compile-time
positive-transfer adapter. Canonical body parsing happens before the first
transcript call, as in the byte verifier, and both roots and all 697 values
come from that one parse.
-/
def semanticScript (positiveTransfer : Bool) (binding : Binding)
    (body : Bytes) : Script Bytes Block Result 1800 :=
  match SameBodySemanticWire.parse body with
  | none => pad (.done (.error .badBody)) 1800
  | some wire =>
    let values := wire.values
    bind (optionalProfileScript positiveTransfer zeroDigest) fun afterPositive =>
      bind (absorbScript afterPositive 1 selectedProfile) fun afterProfile =>
        bind (absorbScript afterProfile 2 (List.ofFn binding)) fun afterStatement =>
          bind (absorbScript afterStatement 3 (List.ofFn (wire.roots 0))) fun afterC1 =>
            bind (candidateScript afterC1) fun lambdaDraw =>
              match lambdaDraw.1 with
              | .error e => .done (.error (.lambda e))
              | .ok lambda =>
                bind (candidateScript lambdaDraw.2) fun chiDraw =>
                  match chiDraw.1 with
                  | .error e => .done (.error (.chi e))
                  | .ok chi =>
                    bind (absorbScript chiDraw.2 9 (List.ofFn (wire.roots 1))) fun afterC2 =>
                      bind (absorbScript afterC2 32 constraintRegistry) fun afterRegistry =>
                        bind (absorbScript afterRegistry 33 helperZero) fun afterHelper =>
                          bind (indexedCandidates 12 0 afterHelper) fun batchDraw =>
                            match batchDraw.1 with
                            | .error (i,e) => .done (.error (.batching i e))
                            | .ok batchValues =>
                              let batching := batchingOfList batchValues
                              let initial := values.getD 0 0
                              bind (absorbScript batchDraw.2 31
                                  (maskClaimRecord initial)) fun afterMask =>
                                bind (nonzeroScript 3 afterMask) fun etaDraw =>
                                  match etaDraw.1 with
                                  | .error e => .done (.error (.eta e))
                                  | .ok eta =>
                                    bind (m := 0)
                                        (semanticRounds body values 10 0 initial etaDraw.2)
                                      fun rounds =>
                                        .done (match rounds with
                                          | .error (r,e) =>
                                            .error (.semanticRound r e)
                                          | .ok state =>
                                            .ok
                                              { lambda := lambda
                                                chi := chi
                                                theta := batching.theta
                                                zc := batching.zc
                                                mu := batching.mu
                                                eta := eta
                                                z := tenCoordinates state.z
                                                finalClaim := state.claim
                                                finalDigest := state.digest })

theorem selectedProfile_length : selectedProfile.length = 25 := by decide
theorem selectedPositiveDescriptor_length : selectedPositiveDescriptor.length = 107 := by decide
theorem constraintRegistry_length : constraintRegistry.length = 28 := by decide
theorem helperZero_length : helperZero.length = 16 := by simp [helperZero]
theorem maskClaimRecord_length (claim : K) : (maskClaimRecord claim).length = 18 := by
  simp [maskClaimRecord, canonicalBytes_length]

theorem semanticRoundBytes_length (body : Bytes) (round : Nat)
    (enough : (1 + 27 * round + 27) * 16 <= body.length) :
    (semanticRoundBytes body round).length = 433 := by
  simp only [semanticRoundBytes, List.length_cons, List.length_take,
    List.length_drop]
  omega

/-- A successful semantic prefix cannot be paired with an independently
supplied field table or roots: it entails one successful same-body wire parse.
The later authentication theorem must still identify these parsed roots with
the chronological commitment cuts. -/
theorem successful_run_has_same_body_wire (positiveTransfer : Bool)
    (binding : Binding) (body : Bytes) (tape : Tape) (oracle : Oracle)
    (success : Success)
    (accepted : (run tape (semanticScript positiveTransfer binding body) oracle).1 =
      some (.ok success)) :
    exists wire, SameBodySemanticWire.parse body = some wire ∧
      fields (body.map UInt8.toFin) = some wire.values := by
  cases parsed : SameBodySemanticWire.parse body with
  | none =>
    exfalso
    have scriptEq : semanticScript positiveTransfer binding body =
        pad (.done (Except.error Error.badBody)) 1800 := by
      simp only [semanticScript, parsed]
    rw [scriptEq, run_pad] at accepted
    change some (Except.error Error.badBody) = some (Except.ok success) at accepted
    exact (by cases accepted)
  | some wire =>
      exact ⟨wire, rfl, SameBodySemanticWire.fields_exact body wire parsed⟩

#print axioms selectedProfile_length
#print axioms selectedPositiveDescriptor_length
#print axioms constraintRegistry_length
#print axioms maskClaimRecord_length
#print axioms semanticRoundBytes_length
#print axioms successful_run_has_same_body_wire

end
end AspisV8Completion.FSLiveSemanticPrefix
