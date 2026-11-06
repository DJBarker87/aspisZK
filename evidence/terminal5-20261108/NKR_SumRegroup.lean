import NKR_SumLookupCertificate
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumRegroup
open FIv_NativeValue (K)
open NKR_SumFinishData

/-- Generic finite sparse-basis contraction. The proof exchanges finite sums
symbolically;no concrete136/272-entry arithmetic term is normalized. -/
theorem contraction {C P : Type} [Fintype C] [Fintype P] [DecidableEq P]
 (out : C → P) (inside : P → Prop) [DecidablePred inside] (term : P → K) (value : C → K) :
 (∑ p : P,if inside p then term p*(∑ c : C,if out c=p then value c else 0) else 0)=
 ∑ c : C,if inside (out c) then term (out c)*value c else 0 := by
 calc
  _=(∑ p : P,∑ c : C,if p=out c then (if inside p then term p*value c else 0) else 0) := by
   apply Finset.sum_congr rfl
   intro p hp
   by_cases h : inside p
   · simp only [if_pos h,Finset.mul_sum]
     apply Finset.sum_congr rfl
     intro c hc
     by_cases equal : out c=p
     · rw [equal]
       simp only [if_true]
     · simp only [if_neg equal,if_neg (Ne.symm equal),mul_zero]
   · simp only [if_neg h]
     symm
     apply Finset.sum_eq_zero
     intro c hc
     split <;> rfl
  _=(∑ c : C,∑ p : P,if p=out c then (if inside p then term p*value c else 0) else 0) := Finset.sum_comm
  _=_ := by
   apply Finset.sum_congr rfl
   intro c hc
   simp

/-- Algebra at each actual endpoint:the high/low selector multiplies BOTH
the tag and compressed pattern;weights independently carry the217binary law. -/
theorem endpoint (high low tag pattern weight : K) :
 high*low*(tag+pattern)=high*tag*low+pattern*(high*low) ∧
 (high*weight)*low=(high*low)*weight := by constructor <;> ring

/--43metadata facts,each only a small index/bound computation. -/
theorem bucket (c : Fin 43) : pOut c∈NJB_PatternReference.coordinates (NKR_SumLookupCertificate.patternGroup c) := by
 fin_cases c <;> decide

theorem bucket_unique (g h : Fin 4) (p : Fin 26)
 (hg : p∈NJB_PatternReference.coordinates g) (hh : p∈NJB_PatternReference.coordinates h) : g=h := by
 have bg : NJB_PatternReference.offset g.castSucc≤p.val ∧ p.val<NJB_PatternReference.offset g.succ := by
  exact of_decide_eq_true (List.mem_filter.mp hg).2
 have bh : NJB_PatternReference.offset h.castSucc≤p.val ∧ p.val<NJB_PatternReference.offset h.succ := by
  exact of_decide_eq_true (List.mem_filter.mp hh).2
 fin_cases g <;> fin_cases h <;> dsimp [NJB_PatternReference.offset] at bg bh ⊢ <;> first | rfl | omega

theorem bucket_iff (g : Fin 4) (c : Fin 43) :
 pOut c∈NJB_PatternReference.coordinates g ↔ NKR_SumLookupCertificate.patternGroup c=g := by
 constructor
 · intro h
   exact bucket_unique _ _ _ (bucket c) h
 · intro h
   rw [←h]
   exact bucket c

#print axioms contraction
#print axioms endpoint
#print axioms bucket
#print axioms bucket_unique
#print axioms bucket_iff
end AspisR1.NKR_SumRegroup
end
