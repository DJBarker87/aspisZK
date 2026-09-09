import Mathlib

/-! Degree of the actual positive-transfer addition along one sumcheck
coordinate. The received message tables are arbitrary constants; no honest
trace, zero residual or decoder premise is used. The successor is the source
polynomial binary increment, not an MLE of a pre-permuted table. -/
set_option autoImplicit false
namespace AspisV8.PositiveResidualDegree
open Polynomial
noncomputable section
variable {K : Type*} [CommRing K] {n : Nat}

def varyingPoint (z : Fin n → K) (j i : Fin n) : K[X] :=
  if i=j then X else C (z i)

def pointValue (z : Fin n → K) (j : Fin n) (x : K) (i : Fin n) : K :=
  if i=j then x else z i

theorem varying_eval (z : Fin n → K) (j i : Fin n) (x : K) :
    (varyingPoint z j i).eval x=pointValue z j x i := by
  by_cases h : i=j <;> simp [varyingPoint,pointValue,h]

theorem varying_degree (z : Fin n → K) (j i : Fin n) :
    (varyingPoint z j i).natDegree ≤ if i=j then 1 else 0 := by
  by_cases h : i=j <;> simp [varyingPoint,h,natDegree_X_le]

theorem add_degree {p q : K[X]} {d : Nat}
    (hp : p.natDegree≤d) (hq : q.natDegree≤d) : (p+q).natDegree≤d :=
  natDegree_add_le_of_degree_le hp hq

theorem sub_degree {p q : K[X]} {d : Nat}
    (hp : p.natDegree≤d) (hq : q.natDegree≤d) : (p-q).natDegree≤d :=
  (natDegree_sub_le p q).trans (max_le hp hq)

/-- A product of distinct coordinate factors has at most one varying factor.
This symbolic support argument is the key to the successor carry bound. -/
theorem product_single_degree (s : Finset (Fin n)) (p : Fin n → K[X])
    (j : Fin n) (hp : ∀ i, (p i).natDegree ≤ (if i=j then 1 else 0)) :
    (∏ i∈s,p i).natDegree≤1 := by
  classical
  calc
    (∏ i∈s,p i).natDegree≤∑ i∈s,(p i).natDegree := natDegree_prod_le s p
    _ ≤ ∑ i∈s,(if i=j then 1 else 0) := Finset.sum_le_sum (fun i _=>hp i)
    _ ≤ 1 := by by_cases h : j∈s <;> simp [h]

def after (i : Fin n) : Finset (Fin n) := Finset.univ.filter (fun l=>i<l)

def carry (p : Fin n → K[X]) (i : Fin n) : K[X] := ∏ l∈after i,p l

def successor (p : Fin n → K[X]) (i : Fin n) : K[X] :=
  p i+carry p i-(p i*carry p i+p i*carry p i)

def successorValue (z : Fin n → K) (i : Fin n) : K :=
  let c:=∏ l∈after i,z l
  z i+c-(z i*c+z i*c)

theorem carry_product_step (p : Fin n → K[X]) (i : Fin n) :
    p i*carry p i=∏ l∈insert i (after i),p l := by
  classical
  have hi : i∉after i := by simp [after]
  simp only [carry,Finset.prod_insert hi]

/-- The closed suffix product also obeys the literal backward loop's carry
update: adjoining the current coordinate multiplies the old carry by it. -/
theorem carry_source_update (p : Fin n → K[X]) (i : Fin n) :
    (∏ l∈Finset.univ.filter (fun l=>i≤l),p l)=p i*carry p i := by
  classical
  have hs : Finset.univ.filter (fun l:Fin n=>i≤l)=insert i (after i) := by
    ext l
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,after]
    omega
  rw [hs,←carry_product_step]

theorem carry_source_initial (p : Fin n → K[X]) :
    (∏ l∈Finset.univ.filter (fun l:Fin n=>n≤l.val),p l)=1 := by
  classical
  have hs : Finset.univ.filter (fun l:Fin n=>n≤l.val)=∅ := by
    ext l
    simp [Nat.not_le.mpr l.isLt]
  rw [hs,Finset.prod_empty]

/-- v6_statement_points handles the last coordinate separately as 1-z[last]
and seeds the next carry with z[last]. This is exactly the generic step. -/
theorem successor_source_last (p : Fin (n+1) → K[X]) :
    successor p ⟨n,by omega⟩=1-p ⟨n,by omega⟩ := by
  classical
  have hs : after (⟨n,by omega⟩ : Fin (n+1))=∅ := by
    ext l
    have hmax := l.isLt
    have hn : ¬(⟨n,by omega⟩ : Fin (n+1))<l := by
      change ¬n<l.val
      omega
    simp [after,hn]
  simp only [successor,carry,hs,Finset.prod_empty]
  ring

theorem successor_eval (z : Fin n → K) (j i : Fin n) (x : K) :
    (successor (varyingPoint z j) i).eval x=successorValue (pointValue z j x) i := by
  simp [successor,carry,successorValue,Polynomial.eval_prod,varying_eval]

theorem successor_degree (z : Fin n → K) (j i : Fin n) :
    (successor (varyingPoint z j) i).natDegree≤1 := by
  have hc : (carry (varyingPoint z j) i).natDegree≤1 :=
    product_single_degree (after i) _ j (varying_degree z j)
  have hp : (varyingPoint z j i*carry (varyingPoint z j) i).natDegree≤1 := by
    rw [carry_product_step]
    exact product_single_degree _ _ j (varying_degree z j)
  have hi : (varyingPoint z j i).natDegree≤1 :=
    (varying_degree z j i).trans (by split_ifs <;> omega)
  exact sub_degree (add_degree hi hc) (add_degree hp hp)

def bitFactor (b : Bool) (p : K[X]) : K[X] := if b then p else 1-p
def bitValue (b : Bool) (v : K) : K := if b then v else 1-v

theorem bit_eval (b : Bool) (p : K[X]) (x : K) :
    (bitFactor b p).eval x=bitValue b (p.eval x) := by
  cases b <;> simp [bitFactor,bitValue]

theorem bit_degree (b : Bool) (p : K[X]) (d : Nat) (hp : p.natDegree≤d) :
    (bitFactor b p).natDegree≤d := by
  cases b
  · exact sub_degree (by simp) hp
  · exact hp

def rowSelector (bits : Fin n → Bool) (p : Fin n → K[X]) : K[X] :=
  ∏ i,bitFactor (bits i) (p i)

def mle (table : (Fin n → Bool) → K) (p : Fin n → K[X]) : K[X] :=
  ∑ bits,C (table bits)*rowSelector bits p

def mleValue (table : (Fin n → Bool) → K) (z : Fin n → K) : K :=
  ∑ bits,table bits*∏ i,bitValue (bits i) (z i)

theorem mle_eval (table : (Fin n → Bool) → K) (p : Fin n → K[X]) (x : K) :
    (mle table p).eval x=mleValue table (fun i=>(p i).eval x) := by
  simp [mle,rowSelector,mleValue,Polynomial.eval_prod,Polynomial.eval_finsetSum,bit_eval]

theorem row_selector_degree (bits : Fin n → Bool) (z : Fin n → K) (j : Fin n) :
    (rowSelector bits (varyingPoint z j)).natDegree≤1 :=
  product_single_degree Finset.univ _ j
    (fun i=>bit_degree _ _ _ (varying_degree z j i))

theorem ordinary_mle_degree (table : (Fin n → Bool) → K) (z : Fin n → K) (j : Fin n) :
    (mle table (varyingPoint z j)).natDegree≤1 := by
  apply natDegree_sum_le_of_forall_le
  intro bits _
  exact (natDegree_C_mul_le _ _).trans (row_selector_degree bits z j)

theorem affine_coordinates_mle_degree (table : (Fin n → Bool) → K)
    (p : Fin n → K[X]) (hp : ∀ i,(p i).natDegree≤1) : (mle table p).natDegree≤n := by
  apply natDegree_sum_le_of_forall_le
  intro bits _
  apply (natDegree_C_mul_le _ _).trans
  calc
    (rowSelector bits p).natDegree≤∑ i:Fin n,(bitFactor (bits i) (p i)).natDegree :=
      natDegree_prod_le _ _
    _ ≤ ∑ _i:Fin n,1 := Finset.sum_le_sum (fun i _=>bit_degree _ _ _ (hp i))
    _ = n := by simp

theorem successor_mle_degree (table : (Fin n → Bool) → K) (z : Fin n → K) (j : Fin n) :
    (mle table (successor (varyingPoint z j))).natDegree≤n :=
  affine_coordinates_mle_degree table _ (successor_degree z j)

def equalityFactor (a : K) (p : K[X]) : K[X] :=
  1-C a-p+C a*p+C a*p

def equalityWeight (zc : Fin n → K) (p : Fin n → K[X]) : K[X] :=
  ∏ i,equalityFactor (zc i) (p i)

theorem equality_factor_degree (a : K) (p : K[X]) (d : Nat) (hp : p.natDegree≤d) :
    (equalityFactor a p).natDegree≤d := by
  have ha : (C a*p).natDegree≤d := (natDegree_C_mul_le _ _).trans hp
  exact add_degree (add_degree (sub_degree (sub_degree (by simp) (by simp)) hp) ha) ha

theorem equality_weight_degree (zc z : Fin n → K) (j : Fin n) :
    (equalityWeight zc (varyingPoint z j)).natDegree≤1 :=
  product_single_degree Finset.univ _ j
    (fun i=>equality_factor_degree _ _ _ (varying_degree z j i))

/-- Big-endian selector matches ROW>>(9-j) in positive_transfer.rs. -/
def row1014Bits (i : Fin 10) : Bool := Nat.testBit 1014 (9-i.val)

/-- At fixed theta/eta, packing slot2 is multiplication by the fixed tower
element u. PositiveTerminalInsertion proves that concrete field identity. -/
def delta (scale : K) (zc z : Fin 10 → K) (j : Fin 10)
    (recipient change inverse : (Fin 10 → Bool) → K) : K[X] :=
  C scale * equalityWeight zc (varyingPoint z j) *
    rowSelector row1014Bits (varyingPoint z j) *
    (mle recipient (varyingPoint z j)*mle change (successor (varyingPoint z j))*
      mle inverse (varyingPoint z j)-1)

theorem positive_delta_degree
    (scale : K) (zc z : Fin 10 → K) (j : Fin 10)
    (recipient change inverse : (Fin 10 → Bool) → K) :
    (delta scale zc z j recipient change inverse).natDegree≤14 := by
  unfold delta
  have hr := ordinary_mle_degree recipient z j
  have hc := successor_mle_degree change z j
  have hu := ordinary_mle_degree inverse z j
  have hrc : (mle recipient (varyingPoint z j)*mle change (successor (varyingPoint z j))).natDegree≤11 :=
    natDegree_mul_le_of_le hr hc
  have hproduct : (mle recipient (varyingPoint z j)*mle change (successor (varyingPoint z j))*
      mle inverse (varyingPoint z j)).natDegree≤12 := natDegree_mul_le_of_le hrc hu
  have hres := sub_degree hproduct (show (1:K[X]).natDegree≤12 by simp)
  have heq : (C scale*equalityWeight zc (varyingPoint z j)).natDegree≤1 :=
    (natDegree_C_mul_le _ _).trans (equality_weight_degree zc z j)
  have hweight : (C scale*equalityWeight zc (varyingPoint z j)*
      rowSelector row1014Bits (varyingPoint z j)).natDegree≤2 :=
    natDegree_mul_le_of_le heq (row_selector_degree _ z j)
  exact natDegree_mul_le_of_le hweight hres

/-- Every remaining-Boolean assignment is summed, not selected for a
favourable challenge. Finite addition cannot increase this degree bound. -/
theorem remaining_assignment_sum_degree {A : Type*} (assignments : Finset A)
    (scale : K) (zc : Fin 10 → K) (z : A → Fin 10 → K) (j : Fin 10)
    (recipient change inverse : (Fin 10 → Bool) → K) :
    (∑ a∈assignments,delta scale zc (z a) j recipient change inverse).natDegree≤14 := by
  apply natDegree_sum_le_of_forall_le
  intro a _
  exact positive_delta_degree scale zc (z a) j recipient change inverse

theorem existing_degree27_grammar_preserved (old addition : K[X])
    (hOld : old.natDegree≤27) (hAdd : addition.natDegree≤14) :
    (old+addition).natDegree≤27 := add_degree hOld (hAdd.trans (by omega))

#print axioms carry_source_initial
#print axioms carry_source_update
#print axioms successor_source_last
#print axioms successor_eval
#print axioms successor_degree
#print axioms mle_eval
#print axioms ordinary_mle_degree
#print axioms successor_mle_degree
#print axioms equality_weight_degree
#print axioms positive_delta_degree
#print axioms remaining_assignment_sum_degree
#print axioms existing_degree27_grammar_preserved
end
end AspisV8.PositiveResidualDegree
