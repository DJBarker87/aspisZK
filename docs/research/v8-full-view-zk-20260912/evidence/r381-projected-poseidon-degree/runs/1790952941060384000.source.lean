import AspisV8R19.R377SelectorCoordinateDegree
import AspisV8R19.R380InternalFifthDegree

/-! One-coordinate degree of the declared exact-field projected Poseidon
expression. Array loops, reductions, packing and source execution are separate
obligations; no source-equivalence or security claim is made here. -/
set_option autoImplicit false
namespace AspisR19.R381ProjectedPoseidonDegree
open Polynomial R374SingleCoordinateDegree R376SimplePointDegree
open R378PairedFifthDegree R380InternalFifthDegree
open AspisV8R19.R377SelectorCoordinateDegree
open scoped BigOperators
noncomputable section
variable {F : Type*} [Field F]

def highCoords : Finset (Fin 10) := Finset.univ.filter (fun i => i.val<6)
def lowCoords : Finset (Fin 10) := Finset.univ.filter (fun i => 6 ≤ i.val)
def highBits (r : Fin 57) (i : Fin 10) : Bool := decide ((r.val/2^(5-i.val))%2=1)
def lowBits (r : Fin 16) (i : Fin 10) : Bool := decide ((r.val/2^(9-i.val))%2=1)
def low (z : Fin 10 → F) (j : Fin 10) (r : Fin 16) : F[X] :=
  selectorPolynomial lowCoords (lowBits r) z j
def block (z : Fin 10 → F) (j : Fin 10) : F[X] :=
  weightedSelectorPolynomial (fun _ : Fin 57 => (1:F)) highBits highCoords z j
def lowWeight (coeff : Fin 16 → F) (z : Fin 10 → F) (j : Fin 10) : F[X] :=
  weightedSelectorPolynomial coeff lowBits lowCoords z j
def localConstants (coeff : Fin 16 → Fin 16 → F) (z : Fin 10 → F)
    (j : Fin 10) : Fin 16 → F[X] := fun i => lowWeight (fun r => coeff r i) z j

theorem split_budget (j : Fin 10) :
    (if j∈highCoords then 1 else 0 : Nat)+(if j∈lowCoords then 1 else 0)=1 := by
  simp only [highCoords,lowCoords,Finset.mem_filter,Finset.mem_univ,true_and]
  by_cases h : j.val<6 <;> simp [h,show (6 ≤ j.val)↔¬(j.val<6) from Nat.not_lt.symm]

theorem localConstants_degree (coeff : Fin 16 → Fin 16 → F)
    (z : Fin 10 → F) (j : Fin 10) (i : Fin 16) :
    (localConstants coeff z j i).natDegree ≤ 1 := by
  exact (weightedSelectorPolynomial_degree _ _ _ _ _).trans (by split_ifs <;> omega)

def ordinary (tables : Fin 16 → Fin 1024 → F) (z : Fin 10 → F)
    (j : Fin 10) : Fin 16 → F[X] := fun i => claimPolynomial (tables i) z j 0
def successor (tables : Fin 16 → Fin 1024 → F) (z : Fin 10 → F)
    (j : Fin 10) : Fin 16 → F[X] := fun i => claimPolynomial (tables i) z j 1

def leading (tables : Fin 16 → Fin 1024 → F) (absorb : Fin 16 → Bool)
    (z : Fin 10 → F) (j : Fin 10) (external : Fin 16 → Fin 16 → F)
    (pack : Fin 4 → Fin 16 → F) (c0 c1 : Fin 16 → F) : Fin 4 → F[X] :=
  linearLayer pack (fifthRound external (fun i => C (c1 i))
    (fifthRound external (fun i => C (c0 i))
      (linearLayer external (absorbedState tables absorb z j))))
def full (tables : Fin 16 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (external : Fin 16 → Fin 16 → F) (pack : Fin 4 → Fin 16 → F)
    (c0 c1 : Fin 16 → Fin 16 → F) : Fin 4 → F[X] :=
  linearLayer pack (fifthRound external (localConstants c1 z j)
    (fifthRound external (localConstants c0 z j) (ordinary tables z j)))
def internal (tables : Fin 16 → Fin 1024 → F) (z : Fin 10 → F) (j : Fin 10)
    (matrix : Fin 16 → Fin 16 → F) (pack : Fin 4 → Fin 16 → F)
    (c0 c1 : Fin 16 → Fin 16 → F) : Fin 4 → F[X] :=
  linearLayer pack (internalRound matrix (fun i => decide(i.val=0)) (localConstants c1 z j)
    (internalRound matrix (fun i => decide(i.val=0)) (localConstants c0 z j)
      (ordinary tables z j)))

theorem branch_degrees (tables : Fin 16 → Fin 1024 → F) (absorb : Fin 16 → Bool)
    (z : Fin 10 → F) (j : Fin 10)
    (external matrix : Fin 16 → Fin 16 → F) (pack : Fin 4 → Fin 16 → F)
    (l0 l1 : Fin 16 → F) (f0 f1 i0 i1 : Fin 16 → Fin 16 → F) (k : Fin 4) :
    (leading tables absorb z j external pack l0 l1 k).natDegree ≤ 25 ∧
    (full tables z j external pack f0 f1 k).natDegree ≤ 25 ∧
    (internal tables z j matrix pack i0 i1 k).natDegree ≤ 25 ∧
    (linearLayer pack (successor tables z j) k).natDegree ≤ 10 := by
  have hs : ∀ i, (ordinary tables z j i).natDegree ≤ 1 := fun i =>
    simple_claim_degree (tables i) z j 0 (by decide)
  refine ⟨?_,?_,?_,?_⟩
  · exact linear_degree pack _ (leading_pair_degree tables absorb z j external external external l0 l1) k
  · exact linear_degree pack _ (paired_fifth_degree external external _ _ _
      (localConstants_degree f0 z j) (localConstants_degree f1 z j) hs) k
  · exact linear_degree pack _ (two_internalRounds_degree matrix matrix _ _ _ _ _
      (localConstants_degree i0 z j) (localConstants_degree i1 z j) hs) k
  · exact linear_degree pack _ (fun i => claim_degree (tables i) z j 1) k

def leadingWeight : Fin 16 → F := fun r => if r.val=0 then 1 else 0
def fullWeight : Fin 16 → F := fun r => if r.val=1 ∨ r.val=9 ∨ r.val=10 then 1 else 0
def internalWeight : Fin 16 → F := fun r => if 2 ≤ r.val ∧ r.val ≤ 8 then 1 else 0

def projected (tables : Fin 16 → Fin 1024 → F) (absorb : Fin 16 → Bool)
    (z : Fin 10 → F) (j : Fin 10)
    (external matrix : Fin 16 → Fin 16 → F) (pack : Fin 4 → Fin 16 → F)
    (l0 l1 : Fin 16 → F) (f0 f1 i0 i1 : Fin 16 → Fin 16 → F) (k : Fin 4) : F[X] :=
  let target := linearLayer pack (successor tables z j) k
  block z j * (lowWeight leadingWeight z j*(target-leading tables absorb z j external pack l0 l1 k)
    +lowWeight fullWeight z j*(target-full tables z j external pack f0 f1 k)
    +lowWeight internalWeight z j*(target-internal tables z j matrix pack i0 i1 k))

theorem projected_degree (tables : Fin 16 → Fin 1024 → F) (absorb : Fin 16 → Bool)
    (z : Fin 10 → F) (j : Fin 10)
    (external matrix : Fin 16 → Fin 16 → F) (pack : Fin 4 → Fin 16 → F)
    (l0 l1 : Fin 16 → F) (f0 f1 i0 i1 : Fin 16 → Fin 16 → F) (k : Fin 4) :
    (projected tables absorb z j external matrix pack l0 l1 f0 f1 i0 i1 k).natDegree ≤ 26 := by
  obtain ⟨hl,hf,hi,ht⟩ := branch_degrees tables absorb z j external matrix pack l0 l1 f0 f1 i0 i1 k
  have ht' : (linearLayer pack (successor tables z j) k).natDegree ≤ 25 := ht.trans (by decide)
  have hw (coeff : Fin 16 → F) : (lowWeight coeff z j).natDegree ≤ if j∈lowCoords then 1 else 0 :=
    weightedSelectorPolynomial_degree _ _ _ _ _
  have bound (p : F[X]) (hp : p.natDegree ≤ 25) (coeff : Fin 16 → F) :
      (lowWeight coeff z j*(linearLayer pack (successor tables z j) k-p)).natDegree ≤ 
        (if j∈lowCoords then 1 else 0)+25 := by
    exact natDegree_mul_le.trans (Nat.add_le_add (hw coeff) (sub_bound ht' hp))
  have hb : (block z j).natDegree ≤ if j∈highCoords then 1 else 0 :=
    weightedSelectorPolynomial_degree _ _ _ _ _
  unfold projected
  apply natDegree_mul_le.trans
  have hsum := natDegree_add_le_of_degree_le
    (natDegree_add_le_of_degree_le (bound _ hl leadingWeight) (bound _ hf fullWeight))
    (bound _ hi internalWeight)
  have hbudget := split_budget j
  omega

def equality (z zc : Fin 10 → F) (j : Fin 10) : F[X] :=
  ∏ i : Fin 10, 1-line z j i-C (zc i)+line z j i*C (zc i)+line z j i*C (zc i)

theorem equality_degree (z zc : Fin 10 → F) (j : Fin 10) :
    (equality z zc j).natDegree ≤ 1 := by
  unfold equality
  apply (natDegree_prod_le _ _).trans
  calc
    _  ≤  ∑ i : Fin 10, (if i=j then 1 else 0 : Nat) := by
      apply Finset.sum_le_sum
      intro i _
      have hl := line_degree z j i
      have h1 : (1 : F[X]).natDegree ≤ if i=j then 1 else 0 := by simp
      have hc : (C (zc i)).natDegree ≤ if i=j then 1 else 0 := by simp
      have hp : (line z j i*C (zc i)).natDegree ≤ if i=j then 1 else 0 := by
        apply natDegree_mul_le.trans
        simpa only [natDegree_C,add_zero] using hl
      exact natDegree_add_le_of_degree_le
        (natDegree_add_le_of_degree_le (sub_bound (sub_bound h1 hl) hc) hp) hp
    _ = 1 := by simp

theorem zerocheck_projected_degree (tables : Fin 16 → Fin 1024 → F) (absorb : Fin 16 → Bool)
    (z zc : Fin 10 → F) (j : Fin 10)
    (external matrix : Fin 16 → Fin 16 → F) (pack : Fin 4 → Fin 16 → F)
    (l0 l1 : Fin 16 → F) (f0 f1 i0 i1 : Fin 16 → Fin 16 → F) (k : Fin 4) :
    (equality z zc j*projected tables absorb z j external matrix pack l0 l1 f0 f1 i0 i1 k).natDegree ≤ 27 := by
  exact natDegree_mul_le.trans (Nat.add_le_add (equality_degree z zc j)
    (projected_degree tables absorb z j external matrix pack l0 l1 f0 f1 i0 i1 k))

#print axioms split_budget
#print axioms localConstants_degree
#print axioms branch_degrees
#print axioms projected_degree
#print axioms equality_degree
#print axioms zerocheck_projected_degree
end
end AspisR19.R381ProjectedPoseidonDegree
