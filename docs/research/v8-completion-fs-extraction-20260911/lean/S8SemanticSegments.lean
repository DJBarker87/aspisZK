import S8RunLevelBind
import FSLiveSemanticPrefix

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2200
set_option maxHeartbeats 600000
namespace AspisV8Completion.S8SemanticSegments
open FSOracleExecution FSBoundedTranscript FSTranscriptScript
open FSLiveSemanticPrefix SameBodySemanticWire FSNonzeroQM31 S8RunLevelBind
noncomputable section
abbrev Bytes := List UInt8
abbrev K := FSNonzeroQM31.K
abbrev SError := FSLiveSemanticPrefix.Error
abbrev SResult := FSLiveSemanticPrefix.Result

def beforeC1 (positive : Bool) (binding : Binding) : Script Bytes Block Block 3 :=
  bind (m := 2) (optionalProfileScript positive zeroDigest) fun afterPositive =>
    bind (m := 1) (absorbScript afterPositive 1 selectedProfile) fun afterProfile =>
      absorbScript afterProfile 2 (List.ofFn binding)

structure Phase2 where
  lambda : K
  chi : K
  digest : Block

def throughC2 (wire : SameBodySemanticWire.Wire) (digest : Block) :
    Script Bytes Block (Except SError Phase2) 134 :=
  bind (m := 133) (absorbScript digest 3 (List.ofFn (wire.roots 0))) fun afterC1 =>
    bind (m := 67) (candidateScript afterC1) fun l =>
      match l.1 with
      | .error e => .done (.error (.lambda e))
      | .ok lambda =>
        bind (m := 1) (candidateScript l.2) fun c =>
          match c.1 with
          | .error e => .done (.error (.chi e))
          | .ok chi =>
            map (fun d => Except.ok (Phase2.mk lambda chi d))
              (absorbScript c.2 9 (List.ofFn (wire.roots 1)))

def afterC2 (body : Bytes) (wire : SameBodySemanticWire.Wire) (state : Phase2) :
    Script Bytes Block SResult 1663 :=
  bind (m := 1662) (absorbScript state.digest 32 constraintRegistry) fun afterRegistry =>
    bind (m := 1661) (absorbScript afterRegistry 33 helperZero) fun afterHelper =>
      bind (m := 869) (indexedCandidates 12 0 afterHelper) fun batchDraw =>
        match batchDraw.1 with
        | .error (i,e) => .done (.error (.batching i e))
        | .ok batchValues =>
          let batching := batchingOfList batchValues
          let initial := wire.values.getD 0 0
          bind (m := 868) (absorbScript batchDraw.2 31 (maskClaimRecord initial)) fun afterMask =>
            bind (m := 670) (nonzeroScript 3 afterMask) fun etaDraw =>
              match etaDraw.1 with
              | .error e => .done (.error (.eta e))
              | .ok eta =>
                bind (m := 0) (semanticRounds body wire.values 10 0 initial etaDraw.2) fun rounds =>
                  .done (match rounds with
                    | .error (r,e) => .error (.semanticRound r e)
                    | .ok result => .ok
                        { lambda := state.lambda, chi := state.chi,
                          theta := batching.theta, zc := batching.zc, mu := batching.mu,
                          eta := eta, z := tenCoordinates result.z,
                          finalClaim := result.claim, finalDigest := result.digest })

def factored (positive : Bool) (binding : Binding) (body : Bytes) :
    Script Bytes Block SResult 1800 :=
  match SameBodySemanticWire.parse body with
  | none => pad (.done (.error .badBody)) 1800
  | some wire =>
    bind (m := 1797) (beforeC1 positive binding) fun digest =>
      bind (m := 1663) (throughC2 wire digest) fun second =>
        match second with
        | .error e => .done (.error e)
        | .ok state => afterC2 body wire state

theorem run_beforeC1_then {A : Type} {m : Nat}
    (positive : Bool) (binding : Binding) (next : Block → Script Bytes Block A m)
    (tape : Tape) (initial : Oracle) :
    run tape (bind (beforeC1 positive binding) next) initial =
      run tape
        (bind (optionalProfileScript positive zeroDigest) fun afterPositive =>
          bind (absorbScript afterPositive 1 selectedProfile) fun afterProfile =>
            bind (absorbScript afterProfile 2 (List.ofFn binding)) next)
        initial := by
  unfold beforeC1
  rw [run_bind_associative]
  apply run_bind_congr
  intro afterPositive oracle1
  rw [run_bind_associative]

theorem run_throughC2_then {A : Type} {m : Nat}
    (wire : SameBodySemanticWire.Wire) (digest : Block)
    (next : Except SError Phase2 → Script Bytes Block A m)
    (tape : Tape) (initial : Oracle) :
    run tape (bind (throughC2 wire digest) next) initial =
      run tape
        (bind (m := m + 133)
            (absorbScript digest 3 (List.ofFn (wire.roots 0))) fun afterC1 =>
          bind (m := m + 67) (candidateScript afterC1) fun l =>
            match l.1 with
            | .error e => pad (next (.error (.lambda e))) 67
            | .ok lambda =>
              bind (m := m + 1) (candidateScript l.2) fun c =>
                match c.1 with
                | .error e => pad (next (.error (.chi e))) 1
                | .ok chi =>
                  bind (m := m) (absorbScript c.2 9 (List.ofFn (wire.roots 1))) fun d =>
                    next (.ok (Phase2.mk lambda chi d)))
        initial := by
  unfold throughC2
  rw [run_bind_associative]
  apply run_bind_congr
  intro afterC1 oracle1
  rw [run_bind_associative]
  apply run_bind_congr
  intro l oracle2
  cases l.1 with
  | error e => rfl
  | ok lambda =>
    rw [run_bind_associative]
    apply run_bind_congr
    intro c oracle3
    cases c.1 with
    | error e => rfl
    | ok chi =>
      simp only [run_bind, run_map]
      rw [run_absorb tape ⟨c.2, oracle3⟩]
      rfl

theorem actual_semantic_run_factorises (positive : Bool) (binding : Binding)
    (body : Bytes) (tape : Tape) (initial : Oracle) :
    run tape (semanticScript positive binding body) initial =
      run tape (factored positive binding body) initial := by
  classical
  cases parsed : SameBodySemanticWire.parse body with
  | none => simp only [semanticScript, factored, parsed]
  | some wire =>
    simp only [semanticScript, factored, parsed]
    rw [run_beforeC1_then]
    apply run_bind_congr
    intro afterPositive oracle1
    apply run_bind_congr
    intro afterProfile oracle2
    apply run_bind_congr
    intro afterStatement oracle3
    rw [run_throughC2_then]
    apply run_bind_congr
    intro afterC1 oracle4
    apply run_bind_congr
    intro lambdaDraw oracle5
    cases lambdaDraw.1 with
    | error e => simp only [run_pad, FSOracleExecution.run]
    | ok lambda =>
      apply run_bind_congr
      intro chiDraw oracle6
      cases chiDraw.1 with
      | error e => simp only [run_pad, FSOracleExecution.run]
      | ok chi =>
        apply run_bind_congr
        intro afterC2Digest oracle7
        rfl

#print axioms actual_semantic_run_factorises
#print axioms run_beforeC1_then
#print axioms run_throughC2_then
end
end AspisV8Completion.S8SemanticSegments
