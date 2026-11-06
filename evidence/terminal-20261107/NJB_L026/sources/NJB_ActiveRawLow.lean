import NJB_ActiveModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_ActiveRawLow
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
/-- Reviewed reference for the seven source match arms; only emitted additions. -/
def lowSum (low : Fin 16 → NQ) (c : Fin 7) : Result NQ :=
 match c.val with
 | 0 => do
   let q0 ← FIq_Native.field.QM31.add (low 11) (low 12)
   ok (q0)
 | 1 => do
   let q0 ← FIq_Native.field.QM31.add (low 0) (low 11)
   let q1 ← FIq_Native.field.QM31.add (q0) (low 12)
   ok (q1)
 | 2 => do
   let q0 ← FIq_Native.field.QM31.add (low 0) (low 12)
   ok (q0)
 | 3 => do
   ok (low 11)
 | 4 => do
   let q0 ← FIq_Native.field.QM31.add (low 0) (low 11)
   ok (q0)
 | 5 => do
   let q0 ← FIq_Native.field.QM31.add (low 1) (low 2)
   let q1 ← FIq_Native.field.QM31.add (q0) (low 5)
   let q2 ← FIq_Native.field.QM31.add (q1) (low 6)
   let q3 ← FIq_Native.field.QM31.add (q2) (low 9)
   let q4 ← FIq_Native.field.QM31.add (q3) (low 10)
   let q5 ← FIq_Native.field.QM31.add (q4) (low 13)
   let q6 ← FIq_Native.field.QM31.add (q5) (low 14)
   ok (q6)
 | 6 => do
   let q0 ← FIq_Native.field.QM31.add (low 0) (low 2)
   let q1 ← FIq_Native.field.QM31.add (q0) (low 4)
   let q2 ← FIq_Native.field.QM31.add (q1) (low 6)
   let q3 ← FIq_Native.field.QM31.add (q2) (low 7)
   let q4 ← FIq_Native.field.QM31.add (q3) (low 9)
   let q5 ← FIq_Native.field.QM31.add (q4) (low 10)
   ok (q5)
 | _ => ok FIq_Native.field.QM31.ZERO

theorem low_sum_result (low : Fin 16 → NQ) (hc : ∀ i,Canon (low i)) (c : Fin 7) :
 ∃ out,lowSum low c=ok out ∧ Canon out ∧
 decode out=NJB_ActiveModel.weight (fun i=>decode (low i)) c := by
 fin_cases c
 ·
   obtain ⟨q0,h0,c0,v0⟩ := NJB_StubLaws.qm_add (low 11) (low 12) (hc _) (hc _)
   refine ⟨q0,?_,c0,?_⟩
   · simp [lowSum,h0]
   ·
     simpa [NJB_ActiveModel.weight,R0P.activeMaskLowSum,R0P.activeMaskBasisMasks] using v0
 ·
   obtain ⟨q0,h0,c0,v0⟩ := NJB_StubLaws.qm_add (low 0) (low 11) (hc _) (hc _)
   obtain ⟨q1,h1,c1,v1⟩ := NJB_StubLaws.qm_add (q0) (low 12) (c0) (hc _)
   refine ⟨q1,?_,c1,?_⟩
   · simp [lowSum,h0,h1]
   · simp only [v0] at v1
     simpa [NJB_ActiveModel.weight,R0P.activeMaskLowSum,R0P.activeMaskBasisMasks] using v1
 ·
   obtain ⟨q0,h0,c0,v0⟩ := NJB_StubLaws.qm_add (low 0) (low 12) (hc _) (hc _)
   refine ⟨q0,?_,c0,?_⟩
   · simp [lowSum,h0]
   ·
     simpa [NJB_ActiveModel.weight,R0P.activeMaskLowSum,R0P.activeMaskBasisMasks] using v0
 ·
   refine ⟨low 11,?_,hc _,?_⟩
   · simp [lowSum]
   · simp [NJB_ActiveModel.weight,R0P.activeMaskLowSum,R0P.activeMaskBasisMasks]
 ·
   obtain ⟨q0,h0,c0,v0⟩ := NJB_StubLaws.qm_add (low 0) (low 11) (hc _) (hc _)
   refine ⟨q0,?_,c0,?_⟩
   · simp [lowSum,h0]
   ·
     simpa [NJB_ActiveModel.weight,R0P.activeMaskLowSum,R0P.activeMaskBasisMasks] using v0
 ·
   obtain ⟨q0,h0,c0,v0⟩ := NJB_StubLaws.qm_add (low 1) (low 2) (hc _) (hc _)
   obtain ⟨q1,h1,c1,v1⟩ := NJB_StubLaws.qm_add (q0) (low 5) (c0) (hc _)
   obtain ⟨q2,h2,c2,v2⟩ := NJB_StubLaws.qm_add (q1) (low 6) (c1) (hc _)
   obtain ⟨q3,h3,c3,v3⟩ := NJB_StubLaws.qm_add (q2) (low 9) (c2) (hc _)
   obtain ⟨q4,h4,c4,v4⟩ := NJB_StubLaws.qm_add (q3) (low 10) (c3) (hc _)
   obtain ⟨q5,h5,c5,v5⟩ := NJB_StubLaws.qm_add (q4) (low 13) (c4) (hc _)
   obtain ⟨q6,h6,c6,v6⟩ := NJB_StubLaws.qm_add (q5) (low 14) (c5) (hc _)
   refine ⟨q6,?_,c6,?_⟩
   · simp [lowSum,h0,h1,h2,h3,h4,h5,h6]
   · simp only [v0,v1,v2,v3,v4,v5] at v6
     simpa [NJB_ActiveModel.weight,R0P.activeMaskLowSum,R0P.activeMaskBasisMasks] using v6
 ·
   obtain ⟨q0,h0,c0,v0⟩ := NJB_StubLaws.qm_add (low 0) (low 2) (hc _) (hc _)
   obtain ⟨q1,h1,c1,v1⟩ := NJB_StubLaws.qm_add (q0) (low 4) (c0) (hc _)
   obtain ⟨q2,h2,c2,v2⟩ := NJB_StubLaws.qm_add (q1) (low 6) (c1) (hc _)
   obtain ⟨q3,h3,c3,v3⟩ := NJB_StubLaws.qm_add (q2) (low 7) (c2) (hc _)
   obtain ⟨q4,h4,c4,v4⟩ := NJB_StubLaws.qm_add (q3) (low 9) (c3) (hc _)
   obtain ⟨q5,h5,c5,v5⟩ := NJB_StubLaws.qm_add (q4) (low 10) (c4) (hc _)
   refine ⟨q5,?_,c5,?_⟩
   · simp [lowSum,h0,h1,h2,h3,h4,h5]
   · simp only [v0,v1,v2,v3,v4] at v5
     simpa [NJB_ActiveModel.weight,R0P.activeMaskLowSum,R0P.activeMaskBasisMasks] using v5

def step (high : Fin 7 → NQ) (low : Fin 16 → NQ) (sum : NQ) (c : Fin 7) : Result NQ := do
 let lowSum ← lowSum low c
 let product ← FIq_Native.field.QM31.mul (high c) lowSum
 FIq_Native.field.QM31.add sum product

theorem step_result (high : Fin 7 → NQ) (low : Fin 16 → NQ) (sum : NQ) (c : Fin 7)
 (hh : ∀ i,Canon (high i)) (hl : ∀ i,Canon (low i)) (hs : Canon sum) :
 ∃ out,step high low sum c=ok out ∧ Canon out ∧
 decode out=NJB_ActiveModel.lowStep (fun i=>decode (high i)) (fun i=>decode (low i)) (decode sum) c := by
 obtain ⟨l,call,cl,vl⟩ := low_sum_result low hl c
 obtain ⟨p,cp,hp,vp⟩ := NJB_StubLaws.qm_mul (high c) l (hh _) cl
 obtain ⟨out,co,ho,vo⟩ := NJB_StubLaws.qm_add sum p hs hp
 refine ⟨out,?_,ho,?_⟩
 · simp only [step,call,cp,co,bind_tc_ok]
 · simpa only [NJB_ActiveModel.lowStep,vl,vp] using vo

def run (high : Fin 7 → NQ) (low : Fin 16 → NQ) : List (Fin 7) → NQ → Result NQ
 | [],sum => ok sum
 | c::cs,sum => do let next ← step high low sum c; run high low cs next

theorem run_result (high : Fin 7 → NQ) (low : Fin 16 → NQ) (cs : List (Fin 7)) (sum : NQ)
 (hh : ∀ i,Canon (high i)) (hl : ∀ i,Canon (low i)) (hs : Canon sum) :
 ∃ out,run high low cs sum=ok out ∧ Canon out ∧
 decode out=NJB_ActiveModel.lowRun (fun i=>decode (high i)) (fun i=>decode (low i)) cs (decode sum) := by
 induction cs generalizing sum with
 | nil => exact ⟨sum,rfl,hs,rfl⟩
 | cons c cs ih =>
   obtain ⟨next,call,hn,vn⟩ := step_result high low sum c hh hl hs
   obtain ⟨out,co,ho,vo⟩ := ih next hn
   refine ⟨out,?_,ho,?_⟩
   · simp only [run,call,co,bind_tc_ok]
   · simpa only [NJB_ActiveModel.lowRun,vn] using vo
#print axioms low_sum_result
#print axioms step_result
#print axioms run_result
end AspisR1.NJB_ActiveRawLow
end
