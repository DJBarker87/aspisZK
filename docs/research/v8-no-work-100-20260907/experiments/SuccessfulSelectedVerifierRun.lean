import AuthenticatedEarlyC1Prefix
import SelectedOrdinaryRowAcceptance
import SelectedResidualPrefixClassification

/-!
A successful parsed selected field-verifier run constructs the existing ideal
execution.  Causal prover callbacks return byte bodies at exactly the response
boundaries; the fixed 697-field parser, rather than a supplied field vector,
constructs every compact response and final.  The early C1 word is the literal
root/prefix completion fixed before the later challenges.  The resulting
strategy is constructed by `TypedRelationTerminal.Decoded.fields`.

This is the parsed compact-field boundary, not a Rust/Aeneas translation of
`performance_verifier::verify_parsed`.  The C1 root is read from the selected
wire offset and cannot be changed independently of the constructed early C1.
C1/C2 total-word authentication, complete opening verification, transcript
hashing/sampling, and payment-witness extraction remain outside this leaf.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 250000

namespace AspisV8.SuccessfulSelectedVerifierRun
open Polynomial Finset
open AspisV8.CausalCoveredRecovery AspisV8.CausalOrderedRelation
open AspisV8.SelectedReceivedOracle AspisV8.CanonicalRelationInput
open AspisV8.AuthenticatedEarlyC1Prefix
open AspisV8.EarlyC1LateProjection
open AspisV8.SelectedAcceptedPrefixPartition
open AspisV8.OODInterpolant
noncomputable section

abbrev K := AspisV5ComponentCQM31TowerExact.QM31Exact
abbrev Byte := AspisV5ComponentCQM31Representation.Byte
abbrev Digest208 := AspisPool.V7MerkleQueryGrammar.Digest208
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

/-- Causal prover messages at the five source read boundaries.  Earlier
responses have no future challenge argument. -/
structure Bodies (q : Nat) where
  response0 : K → List Byte
  final256 : K → K → List Byte
  response1 : K → K → OrderedQueryGame.Schedule domain q → K → List Byte
  response2 : K → K → OrderedQueryGame.Schedule domain q → K → K → List Byte
  response3 : K → K → OrderedQueryGame.Schedule domain q → K → K → K → List Byte

/-- Failed parsing is totalized only to define the strategy off successful
paths.  `ParsedAt` below proves that no fallback is used on the actual run. -/
def decoded (body : List Byte) : List K :=
  (CanonicalRelationInput.parseFixed body).getD []

/-- The selected 26-byte C1 root begins immediately after 697 canonical
QM31 fields.  `parseFixed` success implies these positions are in bounds; getD
only totalizes malformed paths, which `ParsedAt` excludes. -/
def bodyC1Root (body : List Byte) : Digest208 :=
  fun byte => body.getD (697 * 16 + byte.val) 0

def Bodies.fields {q : Nat} (b : Bodies q) :
    K → K → TypedRelationTerminal.Fields domain q :=
  fun _gamma _kappa => TypedRelationTerminal.Decoded.fields
    (fun tau => decoded (b.response0 tau))
    (fun tau alpha => decoded (b.final256 tau alpha))
    (fun tau alpha queries rho => decoded (b.response1 tau alpha queries rho))
    (fun tau alpha queries rho a1 => decoded (b.response2 tau alpha queries rho a1))
    (fun tau alpha queries rho a1 a2 =>
      decoded (b.response3 tau alpha queries rho a1 a2))

/-- The actual path's bodies all pass the canonical fixed-field parser.  This
is stronger than merely assuming six response values and a final vector. -/
structure ParsedAt {q : Nat} (b : Bodies q) (tau alpha : K)
    (queries : OrderedQueryGame.Schedule domain q) (rho a1 a2 : K)
    (root : Digest208) : Prop where
  response0 : ∃ values, parseFixed (b.response0 tau) = some values
  final256 : ∃ values, parseFixed (b.final256 tau alpha) = some values
  response1 : ∃ values, parseFixed (b.response1 tau alpha queries rho) = some values
  response2 : ∃ values, parseFixed (b.response2 tau alpha queries rho a1) = some values
  response3 : ∃ values, parseFixed (b.response3 tau alpha queries rho a1 a2) = some values
  root0 : bodyC1Root (b.response0 tau) = root
  rootFinal : bodyC1Root (b.final256 tau alpha) = root
  root1 : bodyC1Root (b.response1 tau alpha queries rho) = root
  root2 : bodyC1Root (b.response2 tau alpha queries rho a1) = root
  root3 : bodyC1Root (b.response3 tau alpha queries rho a1 a2) = root

theorem decoded_length (body : List Byte)
    (parsed : ∃ values, parseFixed body = some values) :
    (decoded body).length = 697 := by
  obtain ⟨values, success⟩ := parsed
  have length := (CanonicalRelationInput.parse_success body values success).2.1
  simpa [decoded, success] using length

theorem ParsedAt.canonical_lengths {q : Nat} {b : Bodies q} {tau alpha : K}
    {queries : OrderedQueryGame.Schedule domain q} {rho a1 a2 : K}
    {root : Digest208} (parsed : ParsedAt b tau alpha queries rho a1 a2 root) :
    (decoded (b.response0 tau)).length = 697 ∧
    (decoded (b.final256 tau alpha)).length = 697 ∧
    (decoded (b.response1 tau alpha queries rho)).length = 697 ∧
    (decoded (b.response2 tau alpha queries rho a1)).length = 697 ∧
    (decoded (b.response3 tau alpha queries rho a1 a2)).length = 697 :=
  ⟨decoded_length _ parsed.response0, decoded_length _ parsed.final256,
    decoded_length _ parsed.response1, decoded_length _ parsed.response2,
    decoded_length _ parsed.response3⟩

/-- All objects fixed before the compact relation continuation.  In
particular C1 is constructed from the actual early answer prefix and root;
C2 remains the explicitly named post-lambda/chi total-word boundary. -/
structure Program (q : Nat) where
  earlyRecords : AnswerPrefix
  c1Root : Digest208
  c2 : C2Received
  data : OODInterpolant.Data (K := K)
  quarter : K
  quarterChecked : quarter * 4 = 1
  weights : Fin 4 → Fin 1024 → K
  claims : Fin 3 → Fin 29 → K
  inactive : K → K
  /-- Gamma and kappa precede every compact relation body, so their
  dependence belongs outside `Bodies`; later bodies retain only challenges
  already revealed at their own read boundary. -/
  bodies : K → K → Bodies q

def Program.baseExecution {q : Nat} (p : Program q) : Execution q where
  c1 := fixedC1 p.earlyRecords p.c1Root
  c2 := p.c2
  data := p.data
  quarter := p.quarter
  quarterChecked := p.quarterChecked
  weights := p.weights
  claims := p.claims
  inactive := p.inactive
  strategy := fun gamma kappa => ((p.bodies gamma kappa).fields gamma kappa).strategy

/-- The strategy is definitionally reconstructed from causal parsed bodies;
no source/ideal strategy equality is requested. -/
def Program.execution {q : Nat} (p : Program q) : Execution q :=
  SelectedOrdinaryRowAcceptance.withFields p.baseExecution
    (fun gamma kappa => (p.bodies gamma kappa).fields gamma kappa)

def Program.sourceAccepts {q : Nat} (p : Program q)
    (gamma kappa tau alpha : K) (queries : OrderedQueryGame.Schedule domain q)
    (rho a1 a2 a3 : K) : Prop :=
  SelectedOrdinaryRowAcceptance.callbackAccepts p.baseExecution
    (fun gamma kappa => (p.bodies gamma kappa).fields gamma kappa)
    gamma kappa tau alpha queries rho a1 a2 a3

/-- Success at the selected field-verifier boundary.  Parser success, checked
OOD geometry, and nonzero challenges are recorded from the actual path; the
terminal field is the source-shaped compact scalar equality. -/
structure SuccessfulAt {q : Nat} (p : Program q)
    (gamma kappa tau alpha : K) (queries : OrderedQueryGame.Schedule domain q)
    (rho a1 a2 a3 : K) : Prop where
  parsed : ParsedAt (p.bodies gamma kappa) tau alpha queries rho a1 a2 p.c1Root
  dataChecked : p.data.Checked
  circles : p.data.x0^2 + p.data.y0^2 = 1 ∧ p.data.x1^2 + p.data.y1^2 = 1
  west : ∀ r, AspisV8.ComponentOODBinding.pointX p.data r ≠ -1
  gammaNonzero : gamma ≠ 0
  kappaNonzero : kappa ≠ 0
  tauNonzero : tau ≠ 0
  rhoNonzero : rho ≠ 0
  terminal : p.sourceAccepts gamma kappa tau alpha queries rho a1 a2 a3

/-- The headline bridge: one successful source-shaped selected run constructs
the exact ideal execution accepted on the same challenges and the complete
five-way accepted-prefix partition.  It also constructs the fixed
pre-OOD/pre-gamma classifier package consumed by residual recovery. -/
theorem successful_selected_verifier_run_constructs_ideal_execution
    {q : Nat} (p : Program q) (Gamma : Finset K)
    (gamma kappa tau alpha : K) (queries : OrderedQueryGame.Schedule domain q)
    (rho a1 a2 a3 : K)
    (success : SuccessfulAt p gamma kappa tau alpha queries rho a1 a2 a3) :
    ∃ e : Execution q,
      e = p.execution ∧
      idealAccepts e gamma kappa tau alpha queries rho [a1,a2,a3] ∧
      ParsedAt (p.bodies gamma kappa) tau alpha queries rho a1 a2 p.c1Root ∧
      (decoded ((p.bodies gamma kappa).response0 tau)).length = 697 ∧
      (decoded ((p.bodies gamma kappa).final256 tau alpha)).length = 697 ∧
      (decoded ((p.bodies gamma kappa).response1 tau alpha queries rho)).length = 697 ∧
      (decoded ((p.bodies gamma kappa).response2 tau alpha queries rho a1)).length = 697 ∧
      (decoded ((p.bodies gamma kappa).response3 tau alpha queries rho a1 a2)).length = 697 ∧
      (∃! branch, idealAccepts e gamma kappa tau alpha queries rho [a1,a2,a3] ∧
        prefixCase e gamma kappa tau alpha branch) ∧
      e.data.Checked ∧
      (∀ r, AspisV8.ComponentOODBinding.pointX e.data r ≠ -1) ∧
      ∃ E : K[X], E ≠ 0 ∧ E.natDegree ≤ 65061549 ∧
        (SelectedResidualPrefixClassification.family e.c1 e.c2).card ≤ 1 ∧
        (SelectedResidualPrefixClassification.sparseSource e.c1 e.c2 Gamma).card ≤ 28 ∧
        ∀ d : OODInterpolant.Data (K := K), ∃ beta : K[X], beta ≠ 0 ∧
          beta.natDegree ≤ 40 ∧
          SelectedMiddleImageRecovery.CandidateClassifies e.c1 e.c2 Gamma
            (SelectedResidualPrefixClassification.family e.c1 e.c2) E beta
            (SelectedResidualPrefixClassification.sparseSource e.c1 e.c2 Gamma) d := by
  let e := p.execution
  have accepted : idealAccepts e gamma kappa tau alpha queries rho [a1,a2,a3] := by
    have source := (SelectedOrdinaryRowAcceptance.callback_accepts_iff
      p.baseExecution (fun gamma kappa => (p.bodies gamma kappa).fields gamma kappa)
      gamma kappa tau alpha queries rho a1 a2 a3).mp
      success.terminal
    simpa only [e, Program.execution, idealAccepts] using source
  have partition := (accepted_partition e gamma kappa tau alpha queries rho [a1,a2,a3]).mp
    accepted
  have lengths := success.parsed.canonical_lengths
  have classifier := SelectedResidualPrefixClassification.exists_source_classifier
    e.c1 e.c2 Gamma
  exact ⟨e, rfl, accepted, success.parsed, lengths.1, lengths.2.1,
    lengths.2.2.1, lengths.2.2.2.1, lengths.2.2.2.2,
    partition, success.dataChecked, success.west, classifier⟩

#print axioms decoded_length
#print axioms ParsedAt.canonical_lengths
#print axioms successful_selected_verifier_run_constructs_ideal_execution
end
end AspisV8.SuccessfulSelectedVerifierRun
