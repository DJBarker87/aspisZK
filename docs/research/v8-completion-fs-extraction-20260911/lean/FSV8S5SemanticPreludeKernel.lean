import FSNonzeroQM31
import FSV8S5ScriptQueryAlphabet

/-!
S5 FIRST ATTEMPT, UNCOMPILED. Source-shaped semantic control kernel for
performance_verifier.rs::semantic, NOT a completed Rust/parser/terminal refinement.
The typed fields, exact field codec, verifier-derived optional descriptor and
pure selected terminal must be bound to their existing source implementations.
No arbitrary hash-calling semantic prelude is accepted as a parameter.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 600000
set_option maxRecDepth 2200
namespace AspisV8Completion.FSV8S5SemanticPreludeKernel
open FSOracleExecution FSBoundedTranscript FSTranscriptScript FSNonzeroQM31
noncomputable section
abbrev Bytes := List UInt8
abbrev HB := FSBoundedTranscript.Block
abbrev K := FSNonzeroQM31.K

def ascii (s : String) : Bytes := s.toList.map (fun c => UInt8.ofNat c.toNat)

def budgetCast {A : Type} {n m : Nat} (h : n=m)
    (p : Script Bytes HB A n) : Script Bytes HB A m := h ▸ p

structure SemanticWire where
  fields : Fin 697 → K
  roots : Fin 2 → Fin 26 → UInt8

structure SemanticState where
  lambda : K
  chi : K
  theta : K
  zc : Fin 10 → K
  mu : K
  eta : K
  z : Fin 10 → K
  claim : K
  digest : HB

inductive SemanticError where
  | sampler (error : FSNonzeroQM31.Error)
  | terminal

/-- Exact selected state-only registry, including two zero trailing bytes. -/
def registry : Bytes := [1,29,95,0,10,27,28,102,0,17,
  48,33,175,20,236,180,29,18,251,234,229,239,81,34,103,18,0,0]

/-- Actual 3x28 terminal projection. The three D claims remain in the 87-field
point-claims record, but are not supplied to this semantic terminal argument. -/
def claims84 (w : SemanticWire) : Fin 84 → K :=
  fun i => w.fields ⟨271+(i.val/28)*29+i.val%28, by omega⟩

def sent27 (w : SemanticWire) (r : Fin 10) : Fin 27 → K :=
  fun i => w.fields ⟨1+27*r.val+i.val, by omega⟩

def semanticCoefficients (claim : K) (sent : Fin 27 → K) : Fin 28 → K :=
  fun i => if h0 : i.val=0 then sent 0
    else if h1 : i.val=1 then claim-(sent 0+sent 0+
      (List.ofFn (fun j : Fin 26 => sent ⟨j.val+1,by omega⟩)).sum)
    else sent ⟨i.val-1,by omega⟩

def eval28 (c : Fin 28 → K) (x : K) : K :=
  (List.ofFn c).reverse.foldl (fun acc coefficient => coefficient+x*acc) 0

/-- Actual ordinary sampler, not a fresh independent value interface. -/
def drawMany : (n : Nat) → HB →
    Script Bytes HB (Except FSNonzeroQM31.Error (List K) × HB) (66*n)
  | 0,digest => .done (.ok [],digest)
  | n+1,digest => budgetCast (by omega) <|
      bind (m:=66*n) (candidateScript digest) fun first =>
        match first.1 with
        | .error e => .done (.error e,first.2)
        | .ok value => map (fun rest =>
            (rest.1.map (fun values => value::values),rest.2))
              (drawMany n first.2)

/-- Ten literal compact rounds, each label 48 before its ordinary challenge.
Any failing sampler preserves its post-failure digest and oracle through run. -/
def rounds (w : SemanticWire) (encode : K → Fin 16 → UInt8) :
    (remaining : Nat) → remaining ≤ 10 → SemanticState →
      Script Bytes HB (Except SemanticError SemanticState × HB) (67*remaining)
  | 0,_,s => .done (.ok s,s.digest)
  | n+1,room,s =>
      let r : Fin 10 := ⟨10-(n+1),by omega⟩
      let sent := sent27 w r
      let payload := UInt8.ofNat r.val ::
        (List.ofFn sent).flatMap (fun k => List.ofFn (encode k))
      budgetCast (by omega) <|
      bind (m:=66+67*n) (absorbScript s.digest 48 payload) fun digest =>
        budgetCast (by omega) <|
        bind (m:=67*n) (candidateScript digest) fun drawn =>
          match drawn.1 with
          | .error e => .done (.error (.sampler e),drawn.2)
          | .ok alpha => rounds w encode n (by omega)
              { s with z := Function.update s.z r alpha
                       claim := eval28 (semanticCoefficients s.claim sent) alpha
                       digest := drawn.2 }

/-- Literal initializer after the optional positivity descriptor. The 1129
index is conservative; a tighter control-flow bound must be proved separately. -/
def beginSemantic (w : SemanticWire) (binding : Fin 32 → UInt8)
    (encode : K → Fin 16 → UInt8) (digest : HB) :
    Script Bytes HB (Except SemanticError SemanticState × HB) 1129 :=
  bind (m:=1128) (absorbScript digest 1 (ascii "AV8/payment-extraction/v1")) fun d =>
  bind (m:=1127) (absorbScript d 2 (List.ofFn binding)) fun d =>
  bind (m:=1126) (absorbScript d 3 (List.ofFn (w.roots 0))) fun d =>
  bind (m:=1060) (candidateScript d) fun lambdaDraw =>
  match lambdaDraw.1 with
  | .error e => .done (.error (.sampler e),lambdaDraw.2)
  | .ok lambda =>
    bind (m:=994) (candidateScript lambdaDraw.2) fun chiDraw =>
    match chiDraw.1 with
    | .error e => .done (.error (.sampler e),chiDraw.2)
    | .ok chi =>
      bind (m:=993) (absorbScript chiDraw.2 9 (List.ofFn (w.roots 1))) fun d =>
      bind (m:=992) (absorbScript d 32 registry) fun d =>
      bind (m:=991) (absorbScript d 33 (List.replicate 16 0)) fun d =>
      bind (m:=199) (drawMany 12 d) fun batch =>
      match batch.1 with
      | .error e => .done (.error (.sampler e),batch.2)
      | .ok values =>
        bind (m:=198)
          (absorbScript batch.2 31 ([27,10]++List.ofFn (encode (w.fields 0)))) fun d =>
        map (fun etaDraw =>
          (match etaDraw.1 with
            | .error e => Except.error (SemanticError.sampler e)
            | .ok eta => Except.ok ({
                lambda := lambda, chi := chi, theta := values.getD 0 0,
                zc := fun i => values.getD (i.val+1) 0, mu := values.getD 11 0,
                eta := eta, z := fun _ => 0, claim := w.fields 0,
                digest := etaDraw.2 } : SemanticState),etaDraw.2))
          (nonzeroScript 3 d)

/-- The terminal is a PURE source adapter, not an arbitrary Script. Its actual
payment evaluator/positivity extension must be instantiated, not assumed valid.
Transcript::new sets the digest to zero; run inherits the SAME oracle state. -/
def semanticPrelude (w : SemanticWire) (binding : Fin 32 → UInt8)
    (encode : K → Fin 16 → UInt8) (positiveDescriptor : Option Bytes)
    (terminal : SemanticState → (Fin 84 → K) → Option K) :
    Script Bytes HB (Except SemanticError SemanticState × HB) 1800 :=
  let zero : HB := fun _ => 0
  let positive : Script Bytes HB HB 1 :=
    match positiveDescriptor with
    | none => .done zero
    | some descriptor => absorbScript zero 1 descriptor
  bind (m:=1799) positive fun digest =>
    bind (m:=670) (beginSemantic w binding encode digest) fun initial =>
      match initial.1 with
      | .error e => .done (.error e,initial.2)
      | .ok state =>
        map (fun last =>
          (match last.1 with
            | .error e => Except.error e
            | .ok result =>
                match terminal result (claims84 w) with
                | none => Except.error SemanticError.terminal
                | some actual => if actual=result.claim then Except.ok result
                    else Except.error SemanticError.terminal,
           last.2)) (rounds w encode 10 (by omega) state)

theorem semantic_prelude_extends_same_history
    (w : SemanticWire) (binding : Fin 32 → UInt8)
    (encode : K → Fin 16 → UInt8) (positiveDescriptor : Option Bytes)
    (terminal : SemanticState → (Fin 84 → K) → Option K)
    (tape : Tape) (initial : Oracle) :
    ∃ suffix, (run tape (semanticPrelude w binding encode positiveDescriptor terminal)
      initial).2.log = initial.log ++ suffix :=
  run_extends tape _ initial

theorem semantic_prelude_static_allowance
    (w : SemanticWire) (binding : Fin 32 → UInt8)
    (encode : K → Fin 16 → UInt8) (positiveDescriptor : Option Bytes)
    (terminal : SemanticState → (Fin 84 → K) → Option K)
    (tape : Tape) (initial : Oracle) :
    (run tape (semanticPrelude w binding encode positiveDescriptor terminal)
      initial).2.log.length ≤ initial.log.length+1800 := call_bound tape _ initial

#print axioms semantic_prelude_extends_same_history
#print axioms semantic_prelude_static_allowance
end
end AspisV8Completion.FSV8S5SemanticPreludeKernel
