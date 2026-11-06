import NKR_SumFinishFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumFinishMeaning
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NKR_SumFinishBatch
open NKR_SumFinishData
abbrev ModelState := (Fin 4 → K) × (Fin 4 → K)

def decoded (s : State) : ModelState := (NJB_StateUpdates.decoded s.1,NJB_StateUpdates.decoded s.2)
def delta (xs lows : Fin 30 → NQ) (b : Fin 9) : K :=
 NGA_SumAlgebra.sumProducts (((NKR_SumCarrier.encode (arguments xs b)).val.zip
 (NKR_SumCarrier.encode (arguments lows b)).val).take (batchCount b))
def stepModel (tags weights lows : Fin 30 → NQ) (b : Fin 9) (s : ModelState) : ModelState :=
 (NJB_StateUpdates.addModel s.1 (batchGroup b) (delta tags lows b),
  NJB_StateUpdates.addModel s.2 (batchGroup b) (delta weights lows b))

theorem step_result (tags weights lows : Fin 30 → NQ) (b : Fin 9) (before : State)
 (ht : ∀ i,Canon (tags i)) (hw : ∀ i,Canon (weights i)) (hl : ∀ i,Canon (lows i))
 (hb : (∀ i,Canon (before.1 i)) ∧ ∀ i,Canon (before.2 i)) :
 ∃ after,step tags weights lows b before=ok after ∧
 (∀ i,Canon (after.1 i)) ∧ (∀ i,Canon (after.2 i)) ∧
 decoded after=stepModel tags weights lows b (decoded before) := by
 have domain := batch_domain b
 obtain ⟨v,_,rv,cv,vv,_⟩ := NKR_SumCarrier.source (arguments tags b) (arguments lows b)
  (batchCount b) domain.1 domain.2.1 (canonical_arguments tags b ht) (canonical_arguments lows b hl)
 obtain ⟨w,_,rw,cw,vw,_⟩ := NKR_SumCarrier.source (arguments weights b) (arguments lows b)
  (batchCount b) domain.1 domain.2.1 (canonical_arguments weights b hw) (canonical_arguments lows b hl)
 obtain ⟨vs,vsCall,vsc,vsv⟩ := NJB_StateUpdates.add_result before.1 (batchGroup b) v hb.1 cv
 obtain ⟨ws,wsCall,wsc,wsv⟩ := NJB_StateUpdates.add_result before.2 (batchGroup b) w hb.2 cw
 refine ⟨(vs,ws),?_,vsc,wsc,?_⟩
 · simp only [NKR_SumFinishBatch.step,rv,rw,vsCall,wsCall,bind_tc_ok]
 · change (NJB_StateUpdates.decoded vs,NJB_StateUpdates.decoded ws)=_
   rw [vsv,wsv,vv,vw]
   rfl

theorem source (tags weights lows : Fin 30 → NQ) (bs : List (Fin 9)) (before : State)
 (ht : ∀ i,Canon (tags i)) (hw : ∀ i,Canon (weights i)) (hl : ∀ i,Canon (lows i))
 (hb : (∀ i,Canon (before.1 i)) ∧ ∀ i,Canon (before.2 i)) :
 ∃ after,NKR_SumFinishFold.run tags weights lows bs before=ok after ∧
 (∀ i,Canon (after.1 i)) ∧ (∀ i,Canon (after.2 i)) ∧
 decoded after=bs.foldl (fun state b=>stepModel tags weights lows b state) (decoded before) := by
 induction bs generalizing before with
 | nil => exact ⟨before,rfl,hb.1,hb.2,rfl⟩
 | cons b bs ih =>
  obtain ⟨next,hn,cnv,cnw,vn⟩ := step_result tags weights lows b before ht hw hl hb
  obtain ⟨after,ha,cav,caw,va⟩ := ih next ⟨cnv,cnw⟩
  refine ⟨after,?_,cav,caw,?_⟩
  · simp only [NKR_SumFinishFold.run,hn,ha,bind_tc_ok]
  · rw [va,vn]
    rfl

#print axioms step_result
#print axioms source
end AspisR1.NKR_SumFinishMeaning
end
