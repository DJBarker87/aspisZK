import NKR_SumFinishPattern
import NKR_SumFinishFold
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumFinishTrace
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon)
open NKR_SumFinishBatch
open NKR_SumFinishData

/-- NKR_finish_batch_cut transcription, source NKR_SumFinish_native.rs.txt:
min4 count,three padded arrays,tag count/order,op kinds[sum,add,sum,add],
SAME argument pairs,coordinate+count,both complete output frames. Field
child Results are separate Invocation clauses,never part of the native cut. -/
def BatchCut (before after : State) (b : Fin 9) (v vr w wr : NQ)
 (kinds : Fin 4 → Nat) (left right : Fin 4 → NQ) (calls next : Nat) : Prop :=
 kinds=![0,1,0,1] ∧ calls=4 ∧ next=batchStart b+batchCount b ∧
 left 1=before.1 (batchGroup b) ∧ right 1=v ∧
 left 3=before.2 (batchGroup b) ∧ right 3=w ∧
 (∀ i,after.1 i=if batchGroup b=i then vr else before.1 i) ∧
 (∀ i,after.2 i=if batchGroup b=i then wr else before.2 i)

/-- Exact two225 calls/two field Results and their native output frame,
with all child clauses instantiated at actual arrays and arguments. -/
def Invocation (tags weights lows : Fin 30 → NQ) (b : Fin 9) (before after : State) : Prop :=
 ∃ v vr w wr,
 NKR_SumCarrier.reference (arguments tags b) (arguments lows b) (batchCount b)=ok v ∧
 FIq_Native.field.QM31.add (before.1 (batchGroup b)) v=ok vr ∧
 NKR_SumCarrier.reference (arguments weights b) (arguments lows b) (batchCount b)=ok w ∧
 FIq_Native.field.QM31.add (before.2 (batchGroup b)) w=ok wr ∧
 BatchCut before after b v vr w wr ![0,1,0,1]
  ![FIq_Native.field.QM31.ZERO,before.1 (batchGroup b),FIq_Native.field.QM31.ZERO,before.2 (batchGroup b)]
  ![FIq_Native.field.QM31.ZERO,v,FIq_Native.field.QM31.ZERO,w] 4 (batchStart b+batchCount b)

theorem batch (tags weights lows : Fin 30 → NQ) (b : Fin 9) (before : State)
 (ht : ∀ i,Canon (tags i)) (hw : ∀ i,Canon (weights i)) (hl : ∀ i,Canon (lows i))
 (hb : (∀ i,Canon (before.1 i)) ∧ ∀ i,Canon (before.2 i)) :
 ∃ after,step tags weights lows b before=ok after ∧
 Invocation tags weights lows b before after ∧
 (∀ i,Canon (after.1 i)) ∧ ∀ i,Canon (after.2 i) := by
 have domain := batch_domain b
 obtain ⟨v,_,rv,cv,_,_⟩ := NKR_SumCarrier.source (arguments tags b) (arguments lows b)
  (batchCount b) domain.1 domain.2.1 (canonical_arguments tags b ht) (canonical_arguments lows b hl)
 obtain ⟨w,_,rw,cw,_,_⟩ := NKR_SumCarrier.source (arguments weights b) (arguments lows b)
  (batchCount b) domain.1 domain.2.1 (canonical_arguments weights b hw) (canonical_arguments lows b hl)
 obtain ⟨vr,ar,cvr,_⟩ := NJB_StubLaws.qm_add (before.1 (batchGroup b)) v (hb.1 _) cv
 obtain ⟨wr,aw,cwr,_⟩ := NJB_StubLaws.qm_add (before.2 (batchGroup b)) w (hb.2 _) cw
 let after : State := (NJB_StateUpdates.set before.1 (batchGroup b) vr,NJB_StateUpdates.set before.2 (batchGroup b) wr)
 refine ⟨after,?_,⟨v,vr,w,wr,rv,ar,rw,aw,?_⟩,?_,?_⟩
 · simp only [step,rv,rw,NJB_StateUpdates.add,ar,aw,bind_tc_ok];rfl
 · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,fun _=>rfl,fun _=>rfl⟩
 · intro i
   dsimp only [after,NJB_StateUpdates.set]
   split <;> first | exact cvr | exact hb.1 i
 · intro i
   dsimp only [after,NJB_StateUpdates.set]
   split <;> first | exact cwr | exact hb.2 i

inductive Trace (tags weights lows : Fin 30 → NQ) : List (Fin 9) → State → State → Prop
 | nil (s) : Trace tags weights lows [] s s
 | cons {b bs before next after} : Invocation tags weights lows b before next →
  Trace tags weights lows bs next after → Trace tags weights lows (b::bs) before after

theorem source (tags weights lows : Fin 30 → NQ) (bs : List (Fin 9)) (before : State)
 (ht : ∀ i,Canon (tags i)) (hw : ∀ i,Canon (weights i)) (hl : ∀ i,Canon (lows i))
 (hb : (∀ i,Canon (before.1 i)) ∧ ∀ i,Canon (before.2 i)) :
 ∃ after,NKR_SumFinishFold.run tags weights lows bs before=ok after ∧
 Trace tags weights lows bs before after ∧ (∀ i,Canon (after.1 i)) ∧ ∀ i,Canon (after.2 i) := by
 induction bs generalizing before with
 | nil => exact ⟨before,rfl,.nil before,hb.1,hb.2⟩
 | cons b bs ih =>
  obtain ⟨next,hn,inv,hcv,hcw⟩ := batch tags weights lows b before ht hw hl hb
  obtain ⟨after,ha,tr,cv,cw⟩ := ih next ⟨hcv,hcw⟩
  exact ⟨after,by simp only [NKR_SumFinishFold.run,hn,ha,bind_tc_ok],.cons inv tr,cv,cw⟩

#print axioms batch
#print axioms source
end AspisR1.NKR_SumFinishTrace
end
