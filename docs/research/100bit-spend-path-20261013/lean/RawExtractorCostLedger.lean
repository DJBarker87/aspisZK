import ActualCompPolyGCDTotalRemainderCost
import ActualLongDivisionTotalCostV2
import ActualCompPolyPowCost
import RRProgramQueryBound

/-! Partial arithmetic ledgers become a whole-attempt bound only after the
explicit instrumentation and overhead premises in RawExtractorCostComposed.
No claim here identifies modular multiplication counts with field operations. -/
namespace AspisR1.RawExtractorCostLedger
open CompPoly

variable {F : Type} [Field F] [BEq F] [LawfulBEq F] [DecidableEq F]

structure DivisionJob (F : Type) [Field F] [BEq F] [LawfulBEq F] where
  p : CPolynomial.Raw F
  q : CPolynomial.Raw F
  p_trim : p.trim = p
  q_trim : q.trim = q
  monic : q.leadingCoeff = 1
  nonempty : 0 < q.size

structure PowerJob (F : Type) [Field F] [BEq F] [LawfulBEq F] where
  M : CPolynomial.Raw.MulContext F
  D : CPolynomial.Raw.ModContext F
  modulus : CPolynomial.Raw F
  base : CPolynomial.Raw F
  exponent : Nat

def gcdCharge (pq : CPolynomial.Raw F × CPolynomial.Raw F) : Nat :=
  (ActualCompPolyGCDCostMirror.gcdMonicWithCostPublic pq.1 pq.2).2

def divisionCharge (j : DivisionJob F) : Nat :=
  (ActualRawLongDivisionCostV2.divModByMonicAuxWithCost j.p.size j.p j.q).2

def powerCharge (j : PowerJob F) : Nat :=
  (ExtractorPowComplexity.powModWithCost j.M j.D j.modulus j.base j.exponent).2

def gcdBudget (n : Nat) : Nat :=
  (2*n+1)*(100*n^3 + 800*n^2 + 1606*n + 5)

def divisionBudget (n : Nat) : Nat := n * (100 * (n+4) * (n+4))

/-- Convert pointwise natural charges to a bounded total; duplicate jobs count
as distinct occurrences, and aborted prefixes are included. -/
theorem sum_charge_le {A : Type} (xs : List A) (charge : A → Nat)
    (count budget : Nat) (hc : xs.length ≤ count)
    (hb : ∀ x ∈ xs, charge x ≤ budget) :
    (xs.map charge).sum ≤ count * budget := by
  have h : ∀ ys : List A, (∀ x ∈ ys, charge x ≤ budget) →
      (ys.map charge).sum ≤ ys.length * budget := by
    intro ys
    induction ys with
    | nil => intro _; simp
    | cons x ys ih =>
      intro hy
      have ht := ih (fun y hm => hy y (List.mem_cons_of_mem x hm))
      have hh := hy x List.mem_cons_self
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [Nat.add_mul, Nat.one_mul]
      omega
  exact (h xs hb).trans (Nat.mul_le_mul_right budget hc)

/-- Turn the RR program's actual ask-count bound into weighted call work.
The premise is a per-ask implementation bridge, not an expected-value bound.
Thus no independence assumption is needed and aborting branches are covered. -/
theorem rr_trace_to_work {I A S X : Type}
    (zeroTest : S → Bool)
    (children : S → AspisV8R19.MemoizedProgramLaw.Program I A
      (Option (List (X × S)))) (mass : S → Nat)
    (hlocal : ∀ s, AspisR1.ProgramQueryCost.AllCosts (children s)
      (fun out n => n ≤ mass s ∧ ∀ cs, out = some cs →
        AspisR1.RRProgramAbortBound.childMass mass cs ≤ mass s))
    (d : Nat) (s : S) (cursor : Nat) (H : Nat → A)
    (work perAsk fixed : Nat)
    (hwork : work ≤
      (AspisV8R19.MemoizedProgramLaw.eval H
        (AspisR1.SequentialFreshProgram.sequential
          (AspisR1.RRProgramTraversal.collectProgram zeroTest children d s)
          cursor)).1.length * perAsk + fixed) :
    work ≤ (d * mass s) * perAsk + fixed := by
  exact hwork.trans (Nat.add_le_add_right (Nat.mul_le_mul_right perAsk
    (AspisR1.RRProgramQueryBound.collectProgram_actual_trace_bound
      zeroTest children mass hlocal d s cursor H)) fixed)

structure Jobs (F : Type) [Field F] [BEq F] [LawfulBEq F] where
  gcds : List (CPolynomial.Raw F × CPolynomial.Raw F)
  divisions : List (DivisionJob F)
  powers : List (PowerJob F)

def Jobs.charge (j : Jobs F) (modMulFieldBudget : Nat) : Nat :=
  (j.gcds.map gcdCharge).sum + (j.divisions.map divisionCharge).sum +
    (j.powers.map powerCharge).sum * modMulFieldBudget

/-- Named missing scheduling invariant. Sizes concern stored arrays, not just
degrees; the power bound concerns exponent bit length. -/
structure Jobs.Bounded (j : Jobs F) (n b count : Nat) : Prop where
  gcd_count : j.gcds.length ≤ count
  division_count : j.divisions.length ≤ count
  power_count : j.powers.length ≤ count
  gcd_sizes : ∀ pq ∈ j.gcds, pq.1.size ≤ n ∧ pq.2.size ≤ n
  division_sizes : ∀ d ∈ j.divisions, d.p.size ≤ n
  power_bits : ∀ p ∈ j.powers, Nat.log2 p.exponent + 1 ≤ b

theorem jobs_charge_le (j : Jobs F) (n b count mulBudget : Nat)
    (h : j.Bounded n b count) :
    j.charge mulBudget ≤ count * gcdBudget n + count * divisionBudget n +
      (count * (2*b)) * mulBudget := by
  have hg := sum_charge_le j.gcds gcdCharge count (gcdBudget n) h.gcd_count
    (fun pq hp => ActualCompPolyGCDTotalRemainderCost.public_gcd_remainder_cost_uniform
      pq.1 pq.2 n (h.gcd_sizes pq hp).1 (h.gcd_sizes pq hp).2)
  have hd := sum_charge_le j.divisions divisionCharge count (divisionBudget n)
    h.division_count (by
      intro d hd
      have hraw := ActualLongDivisionTotalCostV1.public_division_total_cost
        d.p d.q d.p_trim d.q_trim d.monic d.nonempty
      have hs := h.division_sizes d hd
      exact hraw.trans (Nat.mul_le_mul hs (Nat.mul_le_mul
        (Nat.mul_le_mul_left 100 (Nat.add_le_add_right hs 4))
        (Nat.add_le_add_right hs 4))))
  have hp := sum_charge_le j.powers powerCharge count (2*b) h.power_count (by
    intro p hp
    exact (ExtractorPowComplexity.powModWithCost_le_log_bound
      p.M p.D p.modulus p.base p.exponent).trans
      (Nat.mul_le_mul_left 2 (h.power_bits p hp)))
  exact Nat.add_le_add (Nat.add_le_add hg hd) (Nat.mul_le_mul_right mulBudget hp)

#print axioms rr_trace_to_work
#print axioms sum_charge_le
#print axioms jobs_charge_le
end AspisR1.RawExtractorCostLedger
