import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic

namespace AspisV8.GaoRecovery
open Polynomial Finset
noncomputable section
variable {K : Type*} [Field K] [DecidableEq K]

def errors {n : ℕ} (x y : Fin n → K) (P : K[X]) : Finset (Fin n) :=
  univ.filter fun j => P.eval (x j) ≠ y j

/-- Joint key equation: the received word need not itself be a polynomial.
The stopped remainder is identified by its evaluations and degree, without
assuming that a successful decoder candidate already exists. -/
theorem key_equation {n k t : ℕ} (hk : 0<k) (budget : k+2*t≤n)
    (x y : Fin n → K) (distinct : Function.Injective x) (P r l : K[X])
    (hP : P.natDegree<k) (herr : (errors x y P).card≤t)
    (hr : 2*r.natDegree<n+k) (hl : l.natDegree≤t)
    (evals : ∀ j, r.eval (x j)=l.eval (x j)*y j) : r=l*P := by
  classical
  let good := univ.filter fun j => P.eval (x j)=y j
  have count : good.card+(errors x y P).card=n := by
    simpa [good,errors] using card_filter_add_card_filter_not
      (s := univ) (fun j : Fin n => P.eval (x j)=y j)
  have proddeg : (l*P).natDegree≤l.natDegree+P.natDegree := natDegree_mul_le
  apply eq_of_natDegree_lt_card_of_eval_eq r (l*P)
    (f := fun j : good => x j) (distinct.comp Subtype.val_injective)
  · intro j
    rw [evals, eval_mul, (mem_filter.mp j.property).2]
  · rw [Fintype.card_coe]
    apply max_lt <;> omega

structure State where
  r0 : K[X]
  r1 : K[X]
  t0 : K[X]
  t1 : K[X]

def advance (s : State (K := K)) : State (K := K) :=
  ⟨s.r1, s.r0 % s.r1, s.t1, s.t0-(s.r0/s.r1)*s.t1⟩

def determinant (s : State (K := K)) : K[X] := s.r0*s.t1-s.r1*s.t0

theorem remainder_identity (a b : K[X]) : a%b=a-(a/b)*b := by
  have h := EuclideanDomain.div_add_mod a b
  linear_combination h

theorem advance_determinant (s : State (K := K)) :
    determinant (advance s) = -determinant s := by
  simp only [determinant,advance,remainder_identity]
  ring

theorem advance_evals {n : ℕ} (x y : Fin n → K) (s : State (K := K))
    (h0 : ∀ j, s.r0.eval (x j)=s.t0.eval (x j)*y j)
    (h1 : ∀ j, s.r1.eval (x j)=s.t1.eval (x j)*y j) :
    ∀ j, (advance s).r1.eval (x j)=(advance s).t1.eval (x j)*y j := by
  intro j
  simp only [advance,remainder_identity,eval_sub,eval_mul,h0,h1]
  ring

theorem quotient_degree (a b : K[X]) (ha : a≠0) (hb : b≠0)
    (order : b.natDegree≤a.natDegree) : (a/b).natDegree+b.natDegree=a.natDegree := by
  have order' : b.degree≤a.degree := by
    rw [degree_eq_natDegree ha,degree_eq_natDegree hb]
    exact_mod_cast order
  have hq : a/b≠0 := fun h => not_lt_of_ge order' ((Polynomial.div_eq_zero_iff hb).mp h)
  have h := degree_add_div hb order'
  rw [degree_eq_natDegree ha,degree_eq_natDegree hb,degree_eq_natDegree hq] at h
  have hn : b.natDegree+(a/b).natDegree=a.natDegree := by exact_mod_cast h
  omega

theorem advance_cross_degree (s : State (K := K)) (n : ℕ)
    (h0 : s.r0≠0) (h1 : s.r1≠0) (positive : 0<s.r1.natDegree)
    (order : s.r1.natDegree≤s.r0.natDegree)
    (cross0 : s.r0.natDegree+s.t1.natDegree≤n)
    (cross1 : s.r1.natDegree+s.t0.natDegree≤n) :
    (advance s).r0.natDegree+(advance s).t1.natDegree≤n ∧
    (advance s).r1.natDegree+(advance s).t0.natDegree≤n := by
  have hd := quotient_degree s.r0 s.r1 h0 h1 order
  have hm : ((s.r0/s.r1)*s.t1).natDegree≤(s.r0/s.r1).natDegree+s.t1.natDegree := natDegree_mul_le
  have hs := natDegree_sub_le s.t0 ((s.r0/s.r1)*s.t1)
  have hr := natDegree_mod_lt s.r0 (Nat.ne_of_gt positive)
  constructor
  · change s.r1.natDegree+(s.t0-(s.r0/s.r1)*s.t1).natDegree≤n
    omega
  · change (s.r0%s.r1).natDegree+s.t1.natDegree≤n
    omega

structure Valid {n k : ℕ} (x y : Fin n → K) (s : State (K := K)) : Prop where
  small : s.r1.natDegree<n
  order : s.r1.natDegree≤s.r0.natDegree
  cross0 : s.r0.natDegree+s.t1.natDegree≤n
  cross1 : s.r1.natDegree+s.t0.natDegree≤n
  previous : n+k≤2*s.r0.natDegree
  det : determinant s≠0
  eval0 : ∀ j, s.r0.eval (x j)=s.t0.eval (x j)*y j
  eval1 : ∀ j, s.r1.eval (x j)=s.t1.eval (x j)*y j

abbrev Stop (n k : ℕ) (s : State (K := K)) : Prop := s.r1=0 ∨ 2*s.r1.natDegree<n+k

theorem advance_valid {n k : ℕ} (hk : 0<k) (x y : Fin n → K) (s : State (K := K))
    (v : Valid (k := k) x y s) (go : ¬Stop n k s) : Valid (k := k) x y (advance s) := by
  have h1 : s.r1≠0 := fun h => go (Or.inl h)
  have large : n+k≤2*s.r1.natDegree := by unfold Stop at go; omega
  have positive : 0<s.r1.natDegree := by omega
  have h0 : s.r0≠0 := by intro h; have ho:=v.order; simp [h] at ho; omega
  have cross := advance_cross_degree s n h0 h1 positive v.order v.cross0 v.cross1
  have rem := natDegree_mod_lt s.r0 (Nat.ne_of_gt positive)
  refine ⟨?_,?_,cross.1,cross.2,large,?_,v.eval1,advance_evals x y s v.eval0 v.eval1⟩
  · change (s.r0%s.r1).natDegree<n; exact rem.trans v.small
  · change (s.r0%s.r1).natDegree≤s.r1.natDegree; omega
  · rw [advance_determinant]; exact neg_ne_zero.mpr v.det

def run (n k : ℕ) : ℕ → State (K := K) → Option (State (K := K))
  | 0, _ => none
  | fuel+1, s => if Stop n k s then some s else run n k fuel (advance s)

theorem run_complete {n k : ℕ} (hk : 0<k) (x y : Fin n → K) (fuel : ℕ) :
    ∀ s : State (K := K), Valid (k := k) x y s → s.r1.natDegree<fuel →
    ∃ out, run n k fuel s=some out ∧ Valid (k := k) x y out ∧ Stop n k out := by
  induction fuel with
  | zero => intro s v h; omega
  | succ fuel ih =>
    intro s v h
    by_cases hs : Stop n k s
    · exact ⟨s,by simp [run,hs],v,hs⟩
    · have pos : 0<s.r1.natDegree := by unfold Stop at hs; omega
      have rem := natDegree_mod_lt s.r0 (Nat.ne_of_gt pos)
      obtain ⟨out,he,hv,ht⟩ := ih (advance s) (advance_valid hk x y s v hs)
        (by change (s.r0%s.r1).natDegree<fuel; omega)
      exact ⟨out,by simpa [run,hs] using he,hv,ht⟩

theorem locator_nonzero {n k : ℕ} (x y : Fin n → K) (distinct : Function.Injective x)
    (s : State (K := K)) (v : Valid (k := k) x y s) : s.t1≠0 := by
  intro ht
  have hr : s.r1=0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero s.r1 distinct
    (by intro j; simpa [ht] using v.eval1 j) (by simpa using v.small)
  exact v.det (by simp [determinant,ht,hr])

theorem stopped_quotient {n k : ℕ} (hk : 0<k) (hkn : k≤n)
    (x y : Fin n → K) (distinct : Function.Injective x) (P : K[X])
    (hP : P.natDegree<k) (herr : (errors x y P).card≤(n-k)/2)
    (s : State (K := K)) (v : Valid (k := k) x y s) (hs : Stop n k s) :
    s.t1≠0 ∧ s.t1.natDegree≤(n-k)/2 ∧ s.r1=s.t1*P ∧ s.r1/s.t1=P := by
  have ht := locator_nonzero x y distinct s v
  have hl : s.t1.natDegree≤(n-k)/2 := by have a:=v.cross0; have b:=v.previous; omega
  have hr : 2*s.r1.natDegree<n+k := by rcases hs with h|h; simp [h]; omega; exact h
  have eq := key_equation hk (by omega : k+2*((n-k)/2)≤n) x y distinct P s.r1 s.t1 hP herr hr hl v.eval1
  refine ⟨ht,hl,eq,?_⟩
  rw [eq,mul_div_cancel_left₀ P ht]

def vanishing {n : ℕ} (x : Fin n → K) : K[X] := ∏ j, (X-C (x j))
def interpolant {n : ℕ} (x y : Fin n → K) : K[X] := Lagrange.interpolate univ x y
def initial {n : ℕ} (x y : Fin n → K) : State (K := K) :=
  ⟨vanishing x,interpolant x y,0,1⟩

theorem vanishing_degree {n : ℕ} (x : Fin n → K) : (vanishing x).natDegree=n := by
  simpa [vanishing] using natDegree_finsetProd_X_sub_C_eq_card (s := univ) (f := x)

theorem vanishing_eval {n : ℕ} (x : Fin n → K) (j : Fin n) : (vanishing x).eval (x j)=0 := by
  simp only [vanishing,eval_prod,eval_sub,eval_X,eval_C]
  exact Finset.prod_eq_zero (Finset.mem_univ j) (sub_self (x j))

theorem initial_valid {n k : ℕ} (hk : 0<k) (hkn : k≤n)
    (x y : Fin n → K) (distinct : Function.Injective x) : Valid (k := k) x y (initial x y) := by
  have hd : (interpolant x y).natDegree≤n-1 := by
    apply natDegree_le_of_degree_le
    simpa [interpolant] using Lagrange.degree_interpolate_le y (distinct.injOn (s := (univ : Finset (Fin n))))
  have hr : (interpolant x y).natDegree<n := by omega
  have hv := vanishing_degree x
  have hnz : vanishing x≠0 := (monic_prod_X_sub_C x univ).ne_zero
  constructor
  · exact hr
  · change (interpolant x y).natDegree≤(vanishing x).natDegree; omega
  · simpa [initial,hv]
  · change (interpolant x y).natDegree+(0 : K[X]).natDegree≤n; simp only [natDegree_zero]; omega
  · change n+k≤2*(vanishing x).natDegree; omega
  · simpa [determinant,initial] using hnz
  · intro j; simp [initial,vanishing_eval]
  · intro j
    simpa [initial,interpolant] using Lagrange.eval_interpolate_at_node y
      (distinct.injOn (s := (univ : Finset (Fin n)))) (Finset.mem_univ j)

def decode {n : ℕ} (x y : Fin n → K) (k : ℕ) : Option K[X] :=
  (run n k n (initial x y)).map fun s => s.r1/s.t1

/-- Bounded algorithmic completeness, not merely uniqueness or a theorem
conditioned on an already successful return. The word y may be arbitrary. -/
theorem decoder_complete {n k : ℕ} (hk : 0<k) (hkn : k≤n)
    (x y : Fin n → K) (distinct : Function.Injective x) (P : K[X])
    (hP : P.natDegree<k) (herr : (errors x y P).card≤(n-k)/2) :
    decode x y k=some P := by
  have vi := initial_valid hk hkn x y distinct
  obtain ⟨out,hr,vo,stop⟩ := run_complete hk x y n (initial x y) vi vi.small
  have result := stopped_quotient hk hkn x y distinct P hP herr out vo stop
  simp [decode,hr,result.2.2.2]

#print axioms key_equation
#print axioms advance_determinant
#print axioms advance_evals
#print axioms quotient_degree
#print axioms advance_cross_degree
#print axioms run_complete
#print axioms stopped_quotient
#print axioms initial_valid
#print axioms decoder_complete
end
end AspisV8.GaoRecovery
