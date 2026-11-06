from pathlib import Path
E=Path(__file__).resolve().parent;indices=[[11,12],[0,11,12],[0,12],[11],[0,11],[1,2,5,6,9,10,13,14],[0,2,4,6,7,9,10]]
s='''import NJB_ActiveModel
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJB_ActiveRawLow
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
/-- Reviewed reference for the seven source match arms; only emitted additions. -/
def lowSum (low : Fin 16 → NQ) (c : Fin 7) : Result NQ :=
 match c.val with
'''
for c,ii in enumerate(indices):
 s+=f' | {c} => do\n';prev=f'low {ii[0]}'
 for k,index in enumerate(ii[1:]):s+=f'   let q{k} ← FIq_Native.field.QM31.add ({prev}) (low {index})\n';prev=f'q{k}'
 s+=f'   pure ({prev})\n'
s+=' | _ => pure FIq_Native.field.QM31.ZERO\n\ntheorem low_sum_result (low : Fin 16 → NQ) (hc : ∀ i,Canon (low i)) (c : Fin 7) :\n ∃ out,lowSum low c=ok out ∧ Canon out ∧\n decode out=NJB_ActiveModel.weight (fun i=>decode (low i)) c := by\n fin_cases c\n'
for c,ii in enumerate(indices):
 s+=' ·\n';prev=f'low {ii[0]}'
 for k,index in enumerate(ii[1:]):
  cp='hc _'if k==0 else f'c{k-1}'
  s+=f'   obtain ⟨q{k},h{k},c{k},v{k}⟩ := NJB_StubLaws.qm_add ({prev}) (low {index}) ({cp}) (hc _)\n';prev=f'q{k}'
 cs='hc _'if len(ii)==1 else f'c{len(ii)-2}'
 s+=f'   refine ⟨{prev},?_,{cs},?_⟩\n'
 hs=','.join(f'h{k}'for k in range(len(ii)-1))
 s+=f'   · simp [lowSum{","+hs if hs else ""}]\n'
 if len(ii)==1:s+='   · simp [NJB_ActiveModel.weight,R0P.activeMaskLowSum,R0P.activeMaskBasisMasks]\n'
 else:
  last=len(ii)-2
  if last:s+='   · simp only ['+','.join(f'v{k}'for k in range(last))+f'] at v{last}\n'
  else:s+='   ·\n'
  s+=f'     simpa [NJB_ActiveModel.weight,R0P.activeMaskLowSum,R0P.activeMaskBasisMasks] using v{last}\n'
s+='''
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
'''
(E/'NJB_ActiveRawLow.lean').write_text(s);print('raw low seven-arm totality/value and native-step induction prepared')
