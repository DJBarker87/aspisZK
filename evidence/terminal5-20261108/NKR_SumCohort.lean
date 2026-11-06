import NKR_SumDispatch
set_option autoImplicit false
noncomputable section
namespace NKR_SumCohort
open Aeneas Aeneas.Std Result
open NKR_SumDispatch
open AspisR1.ExtractedMaskQM31Exact (decode)

theorem singleton (x y : Q) (hx : Canon x) (hy : Canon y) :
 AspisR1SelectedMaskProbe.field.QM31.mul x y=NKJ_Cohort.run [(x,y)] := by
 obtain ⟨out,ho,co,vo⟩ := AspisR1.ExtractedMaskQM31Exact.current_qm_mul_exact x y hx hy
 obtain ⟨out',ho',co',vo'⟩ := NKJ_Cohort.value [(x,y)] (by
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact ⟨hx,hy⟩)
 change decode out'=NGA_SumAlgebra.sumProducts [(x,y)] at vo'
 have val : decode out=decode out' := by
  rw [vo,vo']
  simp only [NGA_SumAlgebra.sumProducts,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
 have same := NKJ_Cohort.injective out out' co co' val
 rw [ho,ho',same]

theorem first_canonical (a : A4) (ha : ∀ q∈a.val,Canon q) : Canon (first a) :=
 ha _ (List.getElem_mem _)

theorem first_pairs (l r : A4) : (l.val.zip r.val).take 1=[(first l,first r)] := by
 rcases l with ⟨ls,hls⟩
 rcases r with ⟨rs,hrs⟩
 cases ls with
 | nil => simp at hls
 | cons a tailL =>
  cases rs with
  | nil => simp at hrs
  | cons b tailR => rfl

/-- Full adopted arithmetic on the exact first count input pairs. No count1
restriction: the real field helpers are consumed for counts2,3,4. -/
theorem source (l r : A4) (count : Nat) (lower : 1≤count) (upper : count≤4)
 (hl : ∀ q∈l.val,Canon q) (hr : ∀ q∈r.val,Canon q) :
 reference l r count=NKJ_Cohort.run ((l.val.zip r.val).take count) := by
 have options : count=1 ∨ count=2 ∨ count=3 ∨ count=4 := by omega
 rcases options with h|h|h|h
 · subst count
   rw [first_pairs]
   exact singleton _ _ (first_canonical l hl) (first_canonical r hr)
 · subst count
   have d := helper_domains l r hl hr 2#usize (by decide)
   have h := NKJ_Cohort.source ((selectedPrefix 2#usize (by decide) l).val.zip (selectedPrefix 2#usize (by decide) r).val)
    (by rw [d.1];decide) d.2
   change native l r 2=_ at h
   rw [native_reference l r 2 hl hr,same_pairs] at h
   exact h
 · subst count
   have d := helper_domains l r hl hr 3#usize (by decide)
   have h := NKJ_Cohort.source ((selectedPrefix 3#usize (by decide) l).val.zip (selectedPrefix 3#usize (by decide) r).val)
    (by rw [d.1];decide) d.2
   change native l r 3=_ at h
   rw [native_reference l r 3 hl hr,same_pairs] at h
   exact h
 · subst count
   have d := NGA_Wrappers.domain l r hl hr
   have h := NKJ_Cohort.source (l.val.zip r.val) (by rw [d.1];decide) d.2
   change native l r 4=_ at h
   rw [native_reference l r 4 hl hr] at h
   have len : (l.val.zip r.val).length=4 := by rw [d.1];rfl
   have take : (l.val.zip r.val).take 4=l.val.zip r.val := by
    simpa only [len] using List.take_length (l.val.zip r.val)
   rw [take]
   exact h

/-- Complete parent result and canonicality, with every child-domain clause
discharged internally. This is the Lean half of225; native dispatcher cuts
are required separately before a composed-row candidate is admissible. -/
theorem result (l r : A4) (count : Nat) (lower : 1≤count) (upper : count≤4)
 (hl : ∀ q∈l.val,Canon q) (hr : ∀ q∈r.val,Canon q) :
 ∃ out,native l r count=ok out ∧ reference l r count=ok out ∧
 NKJ_Cohort.run ((l.val.zip r.val).take count)=ok out ∧ Canon out ∧
 decode out=NGA_SumAlgebra.sumProducts ((l.val.zip r.val).take count) := by
 have domain : ∀ p∈(l.val.zip r.val).take count,Canon p.1 ∧ Canon p.2 := by
  intro p hp
  have hm := List.of_mem_zip (List.mem_of_mem_take hp)
  exact ⟨hl p.1 hm.1,hr p.2 hm.2⟩
 obtain ⟨out,ho,co,vo⟩ := NKJ_Cohort.value _ domain
 have hs := source l r count lower upper hl hr
 exact ⟨out,(native_reference l r count hl hr).trans (hs.trans ho),hs.trans ho,ho,co,vo⟩

#print axioms singleton
#print axioms first_canonical
#print axioms first_pairs
#print axioms source
#print axioms result
end NKR_SumCohort
end
