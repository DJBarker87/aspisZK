import RRActualTraversalWorkM10
import RRFixedTapeRecovery

/-! Actual fixed-tape recovery with full scalar/normalization/traversal work.
The initial scan is charged in stored slots. All cap expressions are symbolic
protocol constants and are never normalized into concrete row grids. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.RRRecoveryWorkM10
open CompPoly RRConcreteState RRConcreteValidState RRConcreteInitialValidStateFromFacts
open RRReachableStorageM10 AspisV8R19.OracleFiniteSupport
variable {K : Type} [Field K] [BEq K] [LawfulBEq K] [DecidableEq K] [Fintype K]

def cap (D ell d : Nat) : Nat := D+(d+1)*(ell+1)+1

def initialScan (s : RawState K) : Nat :=
  10*(s.maxX+1)*(s.rows.length+1)+
    10*((s.rows.map List.length).sum+s.rows.length+1)

def initialBudget (D : Nat) : Nat := 100*(D+2)^2

theorem initialScan_bound (D : Nat) (s : RawState K) (h : BoundedRows D s) :
    initialScan s ≤ initialBudget D := by
  have hs := RawExtractorCostLedger.sum_charge_le s.rows List.length (D+1) (D+1) h.2.1 h.2.2
  have hx := h.1
  have hr := h.2.1
  have hm : s.maxX+1 ≤ D+1 := by omega
  have hh : s.rows.length+1 ≤ D+2 := by omega
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left 10 hm) hh
  unfold initialScan initialBudget
  nlinarith

def recover (D ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (RRVectorRowPolynomialBridge.inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0)
    (H : {i : Nat // i ∈ Finset.range (d*ell)} → Fin t → K × K) :
    Option (List (List K)) × Nat :=
  let start := initialValidState ell s hd hn
  let tape := extend (Finset.range (d*ell)) H (fun _ => (0,0))
  ((RRActualScalarTraceM10.collect ell q t tape d start 0).1.1,
    initialScan s+RRActualTraversalWorkM10.work (cap D ell d) ell q t tape d start 0)

theorem value (D ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (RRVectorRowPolynomialBridge.inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0)
    (H : {i : Nat // i ∈ Finset.range (d*ell)} → Fin t → K × K) :
    (recover D ell q t d s hd hn H).1 = (RRFixedTapeRecovery.recover ell q t d s hd hn H).1 :=
by
  have hv := RRActualScalarTraceM10.value ell q t
    (extend (Finset.range (d*ell)) H (fun _ => (0,0))) d (initialValidState ell s hd hn) 0
  have hh := congrArg (fun z : Option (List (List K)) × Nat => z.1) hv
  simpa only [recover,RRFixedTapeRecovery.recover] using hh

@[never_extract,noinline] def budget (D ell q t d : Nat) : Nat :=
  initialBudget D+RRTraversalWriterM10.budget ell
    (RRNodeTariffM10.tariff (cap D ell d) ell q t)
    (RRActualTraversalWorkM10.terminalBudget (cap D ell d)) d

theorem work (D ell q t d : Nat) (s : RawState K)
    (hd : ∀ i ≤ s.maxX, (RRVectorRowPolynomialBridge.inputPolynomial s.rows i).natDegree ≤ ell)
    (hn : model s ≠ 0) (hb : BoundedRows D s) (hq : q = Fintype.card K) (hell : 1 ≤ ell)
    (H : {i : Nat // i ∈ Finset.range (d*ell)} → Fin t → K × K) :
    (recover D ell q t d s hd hn H).2 ≤ budget D ell q t d := by
  have hs := initialScan_bound D s hb
  have hb' := RRReachableStorageM10.initial_normalize D s hb
  have hw := RRActualTraversalWorkM10.work_bound ell D d q t
    (initialNormalizeTotal s) hb' (extend (Finset.range (d*ell)) H (fun _ => (0,0)))
    hq hell d (initialValidState ell s hd hn) Reachable.initial (by omega)
  exact Nat.add_le_add hs hw

#print axioms initialScan_bound
#print axioms value
#print axioms work
end AspisR1.RRRecoveryWorkM10
end
