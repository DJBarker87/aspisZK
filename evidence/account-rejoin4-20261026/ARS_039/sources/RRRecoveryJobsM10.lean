import RRRecoveryWorkM10
import GSScalarBatchJobsM10

set_option autoImplicit false
noncomputable section
namespace AspisR1.RRRecoveryJobsM10
open CompPoly RRConcreteState RRConcreteInitialValidStateFromFacts
open AspisV8R19.OracleFiniteSupport GSScalarOperandEnvelopeM10 GSScalarCallScheduleM10
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def calls (ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (RRVectorRowPolynomialBridge.inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0)
    (H : {i : Nat // i ∈ Finset.range (d*ell)} → Fin t → K × K) : List (Call K) :=
  (RRActualScalarTraceM10.collect ell q t (extend (Finset.range (d*ell)) H (fun _ => (0,0)))
    d (initialValidState ell s hd hn) 0).2

theorem length (ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (RRVectorRowPolynomialBridge.inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0) (hq : q = Fintype.card K)
    (H : {i : Nat // i ∈ Finset.range (d*ell)} → Fin t → K × K) :
    (calls ell q t d s hd hn H).length ≤ RRActualScalarTraceBoundsM10.budget ell t d :=
  RRActualScalarTraceBoundsM10.length ell q t _ d _ 0 hq

theorem bounded (ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (RRVectorRowPolynomialBridge.inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0) (hell : 1 ≤ ell)
    (H : {i : Nat // i ∈ Finset.range (d*ell)} → Fin t → K × K) :
    ∀ c ∈ calls ell q t d s hd hn H, Bounded ell q c :=
  RRActualScalarTraceBoundsM10.bounded ell q t _ d _ 0 hell

-- Generic dependent selection avoids normalization of protocol-specialized
-- interpolation terms while assembling the actual successful branch trace.
def select {A B : Type} : (source : Option A) → ((a : A) → source = some a → List B) → List B
  | none,_ => []
  | some a,next => next a rfl

theorem select_property {A B : Type} (source : Option A)
    (next : (a : A) → source = some a → List B) (P : List B → Prop)
    (hn : P []) (hs : ∀ a h, P (next a h)) : P (select source next) := by
  cases source with
  | none => exact hn
  | some a => exact hs a rfl

#print axioms length
#print axioms bounded
#print axioms select_property
end AspisR1.RRRecoveryJobsM10
end
