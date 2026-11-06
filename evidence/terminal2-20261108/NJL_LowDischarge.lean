import NJB_Cuts
import NJB_ActiveRawLow
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_LowDischarge
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
def operation (kind : Nat) (a b : NQ) : Result NQ :=
 if kind=0 then FIq_Native.field.QM31.mul a b else FIq_Native.field.QM31.add a b
/-- Complete entered child Results for the exact K020..033 operand trace.
Every clause is discharged below; no clause is an input hypothesis. -/
def Clauses (high : Fin 7 → NQ) (low : Fin 16 → NQ) (sum : NQ)
 (r : Fin 17 → NQ) (c : Fin 7) : Prop :=
 ∀ j : Fin (NJB_Cuts.lowCount c+1),
 operation (if j.val=NJB_Cuts.lowCount c-1 then 0 else 1)
  (NJB_Cuts.lowLeft high low sum r c j) (NJB_Cuts.lowRight low r c j)=ok (r ⟨j.val,by have := NJB_Cuts.low_count_bound c;omega⟩)
/-- Universal-reply native cut instantiated at the SAME canonical emitted
child Results. K020/021 through K032/033; full unused reply domain is met
by canonical ZERO, not assumed. The cut's exact final reply is consumed. -/
theorem source (high : Fin 7 → NQ) (low : Fin 16 → NQ) (sum : NQ) (c : Fin 7)
 (hh : ∀ i,Canon (high i)) (hl : ∀ i,Canon (low i)) (hs : Canon sum) :
 ∃ r : Fin 17 → NQ, (∀ j,Canon (r j)) ∧ Clauses high low sum r c ∧
 ∀ events calls next out,
 NJB_Cuts.low high low sum r c events calls next out →
 NJB_ActiveRawLow.step high low sum c=ok out := by
 fin_cases c
 ·
   obtain ⟨q0,h0,c0,_⟩ := NJB_StubLaws.qm_add (low 11) (low 12) (hl _) (hl _)
   obtain ⟨p,hp,cp,_⟩ := NJB_StubLaws.qm_mul (high 0) (q0) (hh _) (c0)
   obtain ⟨v,hv,cv,_⟩ := NJB_StubLaws.qm_add sum p hs cp
   let r : Fin 17 → NQ := ![q0,p,v,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO]
   refine ⟨r,?_,?_,?_⟩
   · intro j; fin_cases j <;> dsimp only [r] <;> first | assumption | exact FIv_NativeValue.zero.1
   · intro j; fin_cases j
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h0
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hp
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hv
   · intro events calls next out cut
     have ho := cut.2.2.2.2.2.2.1
     have same : out=v := by simpa [NJB_Cuts.lowCount,r] using ho
     rw [same]
     simp [NJB_ActiveRawLow.step,NJB_ActiveRawLow.lowSum,h0,hp,hv]
 ·
   obtain ⟨q0,h0,c0,_⟩ := NJB_StubLaws.qm_add (low 0) (low 11) (hl _) (hl _)
   obtain ⟨q1,h1,c1,_⟩ := NJB_StubLaws.qm_add (q0) (low 12) (c0) (hl _)
   obtain ⟨p,hp,cp,_⟩ := NJB_StubLaws.qm_mul (high 1) (q1) (hh _) (c1)
   obtain ⟨v,hv,cv,_⟩ := NJB_StubLaws.qm_add sum p hs cp
   let r : Fin 17 → NQ := ![q0,q1,p,v,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO]
   refine ⟨r,?_,?_,?_⟩
   · intro j; fin_cases j <;> dsimp only [r] <;> first | assumption | exact FIv_NativeValue.zero.1
   · intro j; fin_cases j
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h0
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h1
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hp
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hv
   · intro events calls next out cut
     have ho := cut.2.2.2.2.2.2.1
     have same : out=v := by simpa [NJB_Cuts.lowCount,r] using ho
     rw [same]
     simp [NJB_ActiveRawLow.step,NJB_ActiveRawLow.lowSum,h0,h1,hp,hv]
 ·
   obtain ⟨q0,h0,c0,_⟩ := NJB_StubLaws.qm_add (low 0) (low 12) (hl _) (hl _)
   obtain ⟨p,hp,cp,_⟩ := NJB_StubLaws.qm_mul (high 2) (q0) (hh _) (c0)
   obtain ⟨v,hv,cv,_⟩ := NJB_StubLaws.qm_add sum p hs cp
   let r : Fin 17 → NQ := ![q0,p,v,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO]
   refine ⟨r,?_,?_,?_⟩
   · intro j; fin_cases j <;> dsimp only [r] <;> first | assumption | exact FIv_NativeValue.zero.1
   · intro j; fin_cases j
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h0
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hp
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hv
   · intro events calls next out cut
     have ho := cut.2.2.2.2.2.2.1
     have same : out=v := by simpa [NJB_Cuts.lowCount,r] using ho
     rw [same]
     simp [NJB_ActiveRawLow.step,NJB_ActiveRawLow.lowSum,h0,hp,hv]
 ·
   obtain ⟨p,hp,cp,_⟩ := NJB_StubLaws.qm_mul (high 3) (low 11) (hh _) (hl _)
   obtain ⟨v,hv,cv,_⟩ := NJB_StubLaws.qm_add sum p hs cp
   let r : Fin 17 → NQ := ![p,v,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO]
   refine ⟨r,?_,?_,?_⟩
   · intro j; fin_cases j <;> dsimp only [r] <;> first | assumption | exact FIv_NativeValue.zero.1
   · intro j; fin_cases j
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hp
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hv
   · intro events calls next out cut
     have ho := cut.2.2.2.2.2.2.1
     have same : out=v := by simpa [NJB_Cuts.lowCount,r] using ho
     rw [same]
     simp [NJB_ActiveRawLow.step,NJB_ActiveRawLow.lowSum,hp,hv]
 ·
   obtain ⟨q0,h0,c0,_⟩ := NJB_StubLaws.qm_add (low 0) (low 11) (hl _) (hl _)
   obtain ⟨p,hp,cp,_⟩ := NJB_StubLaws.qm_mul (high 4) (q0) (hh _) (c0)
   obtain ⟨v,hv,cv,_⟩ := NJB_StubLaws.qm_add sum p hs cp
   let r : Fin 17 → NQ := ![q0,p,v,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO]
   refine ⟨r,?_,?_,?_⟩
   · intro j; fin_cases j <;> dsimp only [r] <;> first | assumption | exact FIv_NativeValue.zero.1
   · intro j; fin_cases j
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h0
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hp
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hv
   · intro events calls next out cut
     have ho := cut.2.2.2.2.2.2.1
     have same : out=v := by simpa [NJB_Cuts.lowCount,r] using ho
     rw [same]
     simp [NJB_ActiveRawLow.step,NJB_ActiveRawLow.lowSum,h0,hp,hv]
 ·
   obtain ⟨q0,h0,c0,_⟩ := NJB_StubLaws.qm_add (low 1) (low 2) (hl _) (hl _)
   obtain ⟨q1,h1,c1,_⟩ := NJB_StubLaws.qm_add (q0) (low 5) (c0) (hl _)
   obtain ⟨q2,h2,c2,_⟩ := NJB_StubLaws.qm_add (q1) (low 6) (c1) (hl _)
   obtain ⟨q3,h3,c3,_⟩ := NJB_StubLaws.qm_add (q2) (low 9) (c2) (hl _)
   obtain ⟨q4,h4,c4,_⟩ := NJB_StubLaws.qm_add (q3) (low 10) (c3) (hl _)
   obtain ⟨q5,h5,c5,_⟩ := NJB_StubLaws.qm_add (q4) (low 13) (c4) (hl _)
   obtain ⟨q6,h6,c6,_⟩ := NJB_StubLaws.qm_add (q5) (low 14) (c5) (hl _)
   obtain ⟨p,hp,cp,_⟩ := NJB_StubLaws.qm_mul (high 5) (q6) (hh _) (c6)
   obtain ⟨v,hv,cv,_⟩ := NJB_StubLaws.qm_add sum p hs cp
   let r : Fin 17 → NQ := ![q0,q1,q2,q3,q4,q5,q6,p,v,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO]
   refine ⟨r,?_,?_,?_⟩
   · intro j; fin_cases j <;> dsimp only [r] <;> first | assumption | exact FIv_NativeValue.zero.1
   · intro j; fin_cases j
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h0
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h1
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h2
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h3
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h4
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h5
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h6
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hp
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hv
   · intro events calls next out cut
     have ho := cut.2.2.2.2.2.2.1
     have same : out=v := by simpa [NJB_Cuts.lowCount,r] using ho
     rw [same]
     simp [NJB_ActiveRawLow.step,NJB_ActiveRawLow.lowSum,h0,h1,h2,h3,h4,h5,h6,hp,hv]
 ·
   obtain ⟨q0,h0,c0,_⟩ := NJB_StubLaws.qm_add (low 0) (low 2) (hl _) (hl _)
   obtain ⟨q1,h1,c1,_⟩ := NJB_StubLaws.qm_add (q0) (low 4) (c0) (hl _)
   obtain ⟨q2,h2,c2,_⟩ := NJB_StubLaws.qm_add (q1) (low 6) (c1) (hl _)
   obtain ⟨q3,h3,c3,_⟩ := NJB_StubLaws.qm_add (q2) (low 7) (c2) (hl _)
   obtain ⟨q4,h4,c4,_⟩ := NJB_StubLaws.qm_add (q3) (low 9) (c3) (hl _)
   obtain ⟨q5,h5,c5,_⟩ := NJB_StubLaws.qm_add (q4) (low 10) (c4) (hl _)
   obtain ⟨p,hp,cp,_⟩ := NJB_StubLaws.qm_mul (high 6) (q5) (hh _) (c5)
   obtain ⟨v,hv,cv,_⟩ := NJB_StubLaws.qm_add sum p hs cp
   let r : Fin 17 → NQ := ![q0,q1,q2,q3,q4,q5,p,v,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO,FIq_Native.field.QM31.ZERO]
   refine ⟨r,?_,?_,?_⟩
   · intro j; fin_cases j <;> dsimp only [r] <;> first | assumption | exact FIv_NativeValue.zero.1
   · intro j; fin_cases j
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h0
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h1
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h2
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h3
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h4
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using h5
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hp
     · simpa [operation,NJB_Cuts.lowCount,NJB_Cuts.lowLeft,NJB_Cuts.lowRight,NJB_Cuts.lowIndex,NJB_Cuts.lowIndices,r] using hv
   · intro events calls next out cut
     have ho := cut.2.2.2.2.2.2.1
     have same : out=v := by simpa [NJB_Cuts.lowCount,r] using ho
     rw [same]
     simp [NJB_ActiveRawLow.step,NJB_ActiveRawLow.lowSum,h0,h1,h2,h3,h4,h5,hp,hv]
#print source
#print axioms source
end AspisR1.NJL_LowDischarge
end
