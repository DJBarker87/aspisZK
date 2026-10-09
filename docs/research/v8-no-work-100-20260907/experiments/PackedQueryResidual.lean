import PackedQueryRecord
import SelectedQueryBuffer

/-! Canonically parsed query records feed the actual ordered inverse/fold
arithmetic. These are observed local records, not a root-authenticated global
word. The rho identity keeps their ordinal order and an arbitrary prior. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 200
set_option maxHeartbeats 30000
namespace AspisV8.PackedQueryResidual
noncomputable section
open AspisV5ComponentCQM31TowerExact AspisPool.V7MerkleQueryGrammar
open AspisV5FriConcreteEncoderCommutation AspisV5ComponentCConcreteFoldLinearity
open AspisK1.V7Tag73ExactOneFoldEncoderBinding
open AspisV8.OODInterpolant AspisV8.QueriedResidual
open AspisV8.PostQueryFunctional AspisV8.PackedQueryRecord
open scoped BigOperators
abbrev K := QM31Exact
local instance : NeZero (2 : K) := SelectedReceivedOracle.twoNonzero

def interpolated (d : Data (K:=K)) (query : Fin 262144) (slot : Fin 4) : K :=
  d.intercept+d.slope*selected d.useX (xs (exactCircleX query) slot)
    (ys (exactCircleY query) slot)

def sourceSlots {q : Nat} (d : Data (K:=K)) (decoded : Fin q → Decoded)
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (i : Fin q) : Fin 4 → K := fun slot =>
  (combined d.gamma (decoded i) slot-interpolated d (queries i) slot)*inverseAt out i slot

/-- Total raw-byte quotient at one observed fibre. The success theorem
requires the parser and checked inverse; invalid bytes/poles are not accepted. -/
def rawQuotient (d : Data (K:=K)) (record : List Byte)
    (query : Fin 262144) (slot : Fin 4) : K :=
  (rawCombined d.gamma record slot-interpolated d query slot)/sourceDenom d query slot

theorem success_slots {q : Nat} (d : Data (K:=K))
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c (SelectedQueryBuffer.points queries)=some out)
    (i : Fin q) : sourceSlots d decoded queries out i=rawQuotient d (records i) (queries i) := by
  have checked := (SelectedQueryBuffer.inverse_eq d queries).symm.trans inverse
  funext slot
  rw [sourceSlots,combined_eq_raw _ _ (parsed i),
    QueriedResidual.success_inverse d queries (baseList queries) out checked i slot]
  rw [rawQuotient,sourceDenom_eq]
  rfl

-- Inner scalar computations are already identified above. Do not ask the
-- elaborator to normalize packed sums or stored-domain generator powers
-- while transporting the four abstract scalar slots through a fold.
attribute [local irreducible] sourceSlots rawQuotient
attribute [local irreducible] PackedQueryRecord.combined PackedQueryRecord.rawCombined
attribute [local irreducible] exactCircleX exactCircleY

/- The six scalar interface deliberately stops before expanding a concrete
packed-byte expression or a stored-domain generator. -/
@[ext] structure FoldInput (F : Type*) where
  ix : F
  iy : F
  v0 : F
  v1 : F
  v2 : F
  v3 : F

namespace FoldInput
theorem constructor_eq {F : Type*} {ix iy v0 v1 v2 v3 jx jy w0 w1 w2 w3 : F}
    (hx : ix=jx) (hy : iy=jy) (h0 : v0=w0) (h1 : v1=w1) (h2 : v2=w2) (h3 : v3=w3) :
    (⟨ix,iy,v0,v1,v2,v3⟩ : FoldInput F)=⟨jx,jy,w0,w1,w2,w3⟩ := by
  cases hx
  cases hy
  cases h0
  cases h1
  cases h2
  cases h3
  rfl

variable {F : Type*} [Field F]
def expanded (input : FoldInput F) (alpha : F) : F :=
  QuotientFold.expanded (1/2) alpha input.ix input.iy
    input.v0 input.v1 input.v2 input.v3
def circle (input : FoldInput F) (alpha : F) : F :=
  circleFoldValue alpha input.ix input.iy ![input.v0,input.v1,input.v2,input.v3]
theorem expanded_circle (input : FoldInput F) (alpha : F) :
    input.expanded alpha=input.circle alpha := by
  exact QueriedResidual.fused_circle alpha input.ix input.iy
    ![input.v0,input.v1,input.v2,input.v3]
end FoldInput

def sourceInput {q : Nat} (d : Data (K:=K)) (decoded : Fin q → Decoded)
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (i : Fin q) : FoldInput K where
  ix := baseInverseAt out i false
  iy := baseInverseAt out i true
  v0 := sourceSlots d decoded queries out i 0
  v1 := sourceSlots d decoded queries out i 1
  v2 := sourceSlots d decoded queries out i 2
  v3 := sourceSlots d decoded queries out i 3

def rawInput (d : Data (K:=K)) (record : List Byte)
    (query : Fin 262144) : FoldInput K where
  ix := (2*exactCircleX query)⁻¹
  iy := (2*exactCircleY query)⁻¹
  v0 := rawQuotient d record query 0
  v1 := rawQuotient d record query 1
  v2 := rawQuotient d record query 2
  v3 := rawQuotient d record query 3

theorem success_input {q : Nat} (d : Data (K:=K))
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c (SelectedQueryBuffer.points queries)=some out)
    (i : Fin q) : sourceInput d decoded queries out i=rawInput d (records i) (queries i) := by
  have checked := (SelectedQueryBuffer.inverse_eq d queries).symm.trans inverse
  have slot0 := congrFun (success_slots d records decoded parsed queries out inverse i) 0
  have slot1 := congrFun (success_slots d records decoded parsed queries out inverse i) 1
  have slot2 := congrFun (success_slots d records decoded parsed queries out inverse i) 2
  have slot3 := congrFun (success_slots d records decoded parsed queries out inverse i) 3
  have invx := QueriedResidual.success_base_inverse d queries out checked i false
  have invy := QueriedResidual.success_base_inverse d queries out checked i true
  simp only [Bool.false_eq_true,ite_false] at invx
  simp only [ite_true] at invy
  unfold sourceInput rawInput
  cases invx
  cases invy
  cases slot0
  cases slot1
  cases slot2
  cases slot3
  rfl

attribute [local irreducible] sourceInput rawInput

def sourceFold {q : Nat} (d : Data (K:=K)) (decoded : Fin q → Decoded)
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (alpha : K) (i : Fin q) : K :=
  (sourceInput d decoded queries out i).expanded alpha

def rawFold (d : Data (K:=K)) (record : List Byte) (query : Fin 262144) (alpha : K) : K :=
  (rawInput d record query).circle alpha

theorem success_fold {q : Nat} (d : Data (K:=K))
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c (SelectedQueryBuffer.points queries)=some out)
    (alpha : K) (i : Fin q) :
    sourceFold d decoded queries out alpha i=rawFold d (records i) (queries i) alpha := by
  unfold sourceFold rawFold
  rw [success_input d records decoded parsed queries out inverse i]
  exact FoldInput.expanded_circle (rawInput d (records i) (queries i)) alpha

attribute [local irreducible] sourceFold rawFold

def residual {q : Nat} (d : Data (K:=K)) (records : Fin q → List Byte)
    (queries : Fin q → Fin 262144) (alpha : K) (final : Fin 256 → K) : Fin q → K :=
  fun i=>exactFinalLinear final (queries i)-rawFold d (records i) (queries i) alpha

theorem success_residual {q : Nat} (d : Data (K:=K))
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c (SelectedQueryBuffer.points queries)=some out)
    (alpha : K) (final : Fin 256 → K) (i : Fin q) :
    exactFinalLinear final (queries i)-sourceFold d decoded queries out alpha i=
      residual d records queries alpha final i := by
  rw [success_fold d records decoded parsed queries out inverse alpha i]
  unfold residual
  rfl

attribute [local irreducible] residual
attribute [local irreducible] exactFinalLinear lineEval lineWeight storedPoint

section GenericInjection
variable {F : Type*} [Field F] [DecidableEq F]
/-- A symbolic helper only; the selected theorem below derives its residual
premise from the parsed bytes and checked inverse, rather than exposing it. -/
theorem injection_from_residual (n q : Nat) (final weight : Fin n → F)
    (evaluation : Fin q → Fin n → F) (opening errors : Fin q → F)
    (carried rho : F)
    (error_eq : ∀ j, (∑ i, final i*evaluation j i)-opening j=errors j) :
    (carried+∑ j, rho^(j.val+1)*opening j)-
      (∑ i, final i*(weight i+∑ j, rho^(j.val+1)*evaluation j i))=
      (carried-∑ i, final i*weight i)-rho*∑ j, errors j*rho^j.val := by
  apply (ImageCallbackInterfaces.query_injection n q final weight evaluation opening carried rho).trans
  apply congrArg (fun z=>(carried-∑ i, final i*weight i)-rho*z)
  apply Finset.sum_congr rfl
  intro j _
  rw [error_eq j]
end GenericInjection

/-- The proof field is populated by the selected constructor below; it is
not an extra hypothesis exposed at the selected endpoint. -/
structure CertifiedInjection (F : Type*) [Field F] (n q : Nat) where
  final : Fin n → F
  weight : Fin n → F
  evaluation : Fin q → Fin n → F
  opening : Fin q → F
  errors : Fin q → F
  error_eq : ∀ j, (∑ i, final i*evaluation j i)-opening j=errors j

namespace CertifiedInjection
variable {F : Type*} [Field F] [DecidableEq F] {n q : Nat}
def actual (input : CertifiedInjection F n q) (carried rho : F) : F :=
  (carried+∑ j, rho^(j.val+1)*input.opening j)-
    (∑ i, input.final i*(input.weight i+∑ j, rho^(j.val+1)*input.evaluation j i))
def shifted (input : CertifiedInjection F n q) (carried rho : F) : F :=
  (carried-∑ i, input.final i*input.weight i)-rho*∑ j, input.errors j*rho^j.val
theorem boundary (input : CertifiedInjection F n q) (carried rho : F) :
    input.actual carried rho=input.shifted carried rho :=
  injection_from_residual n q input.final input.weight input.evaluation input.opening
    input.errors carried rho input.error_eq
end CertifiedInjection

/-- Exact source injection into an arbitrary existing ordinary/image carried
functional. This does not assume its prior discrepancy was already zero. -/
def injectionInput {q : Nat} (d : Data (K:=K))
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c (SelectedQueryBuffer.points queries)=some out)
    (alpha : K) (final weight : Fin 256 → K) : CertifiedInjection K 256 q where
  final := final
  weight := weight
  evaluation := fun j=>lineWeight (storedPoint (K:=K) (queries j))
  opening := sourceFold d decoded queries out alpha
  errors := residual d records queries alpha final
  error_eq j := by
    have evaluation :
      (∑ i, final i*lineWeight (storedPoint (K:=K) (queries j)) i)=
        exactFinalLinear final (queries j) :=
      (lineEval_dot final _).symm.trans (SelectedReceivedOracle.final_evaluation final (queries j))
    rw [evaluation]
    exact success_residual d records decoded parsed queries out inverse alpha final j

attribute [local irreducible] injectionInput

/-- The concrete constructed input, including its record-ordered errors,
satisfies the degree-q shifted-rho discrepancy identity. -/
theorem query_injection {q : Nat} (d : Data (K:=K))
    (records : Fin q → List Byte) (decoded : Fin q → Decoded)
    (parsed : ∀ i, parse (records i)=some (decoded i))
    (queries : Fin q → Fin 262144) (out : List K × List M31Exact)
    (inverse : LineNormBuffer.inverseLines d.a d.b d.c (SelectedQueryBuffer.points queries)=some out)
    (alpha rho carried : K) (final weight : Fin 256 → K) :
    let input := injectionInput d records decoded parsed queries out inverse alpha final weight
    input.actual carried rho=input.shifted carried rho :=
  CertifiedInjection.boundary
    (injectionInput d records decoded parsed queries out inverse alpha final weight) carried rho

#print axioms success_slots
#print axioms FoldInput.expanded_circle
#print axioms success_input
#print axioms success_fold
#print axioms success_residual
#print axioms injectionInput
#print axioms query_injection
end
end AspisV8.PackedQueryResidual
