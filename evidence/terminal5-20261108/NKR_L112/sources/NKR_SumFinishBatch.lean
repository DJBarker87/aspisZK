import NKR_SumFinishData
import NKR_SumCarrier
import NJB_StubLaws
import NJB_ArrayCarrier
import NJB_StateUpdates
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKR_SumFinishBatch
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode)
open NKR_SumFinishData
abbrev State := (Fin 4 → NQ) × (Fin 4 → NQ)

def padded (xs : Fin 30 → NQ) (b : Fin 9) (i : Fin 4) : NQ :=
 if h : i.val<batchCount b then xs (batchCoordinate b ⟨i.val,h⟩) else FIq_Native.field.QM31.ZERO

def arguments (xs : Fin 30 → NQ) (b : Fin 9) : Array NQ 4#usize :=
 NJB_ArrayCarrier.array (padded xs b)

theorem canonical_arguments (xs : Fin 30 → NQ) (b : Fin 9) (hx : ∀ i,Canon (xs i)) :
 FIw_ArrayValue.canonical (arguments xs b) := by
 apply NJB_ArrayCarrier.canonical_array
 intro i
 unfold padded
 split
 · exact hx _
 · exact FIv_NativeValue.zero.1

/-- Source-order single native dot-batch window: SAME tag/weight/low
arrays, value sum then value add, weight sum then weight add, and full
four-cell frames. Each225 call receives its actual count=min(4,end-start). -/
def step (tags weights lows : Fin 30 → NQ) (b : Fin 9) (before : State) : Result State := do
 let valueSum ← NKR_SumCarrier.reference (arguments tags b) (arguments lows b) (batchCount b)
 let values ← NJB_StateUpdates.add before.1 (batchGroup b) valueSum
 let weightSum ← NKR_SumCarrier.reference (arguments weights b) (arguments lows b) (batchCount b)
 let weights ← NJB_StateUpdates.add before.2 (batchGroup b) weightSum
 ok (values,weights)

/-- Both complete child Results and each caller-established canonical/arity
condition are outputs; no child-success or endpoint premise. The native
one-window certificate for220 remains separately required. -/
theorem source (tags weights lows : Fin 30 → NQ) (b : Fin 9) (before : State)
 (ht : ∀ i,Canon (tags i)) (hw : ∀ i,Canon (weights i)) (hl : ∀ i,Canon (lows i))
 (hb : (∀ i,Canon (before.1 i)) ∧ ∀ i,Canon (before.2 i)) :
 ∃ valueSum weightSum values afterWeights,
 NKR_SumCarrier.reference (arguments tags b) (arguments lows b) (batchCount b)=ok valueSum ∧
 NKR_SumCarrier.reference (arguments weights b) (arguments lows b) (batchCount b)=ok weightSum ∧
 NJB_StateUpdates.add before.1 (batchGroup b) valueSum=ok values ∧
 NJB_StateUpdates.add before.2 (batchGroup b) weightSum=ok afterWeights ∧
 step tags weights lows b before=ok (values,afterWeights) ∧
 (∀ i,Canon (values i)) ∧ (∀ i,Canon (afterWeights i)) ∧
 (∀ i,i≠batchGroup b → values i=before.1 i ∧ afterWeights i=before.2 i) := by
 have domain := batch_domain b
 obtain ⟨v,nv,rv,cv,vv,cutv⟩ := NKR_SumCarrier.source (arguments tags b) (arguments lows b)
  (batchCount b) domain.1 domain.2.1 (canonical_arguments tags b ht) (canonical_arguments lows b hl)
 obtain ⟨w,nw,rw,cw,vw,cutw⟩ := NKR_SumCarrier.source (arguments weights b) (arguments lows b)
  (batchCount b) domain.1 domain.2.1 (canonical_arguments weights b hw) (canonical_arguments lows b hl)
 obtain ⟨v',av,cv',vv'⟩ := NJB_StubLaws.qm_add (before.1 (batchGroup b)) v (hb.1 _) cv
 obtain ⟨w',aw,cw',vw'⟩ := NJB_StubLaws.qm_add (before.2 (batchGroup b)) w (hb.2 _) cw
 let values := NJB_StateUpdates.set before.1 (batchGroup b) v'
 let afterWeights := NJB_StateUpdates.set before.2 (batchGroup b) w'
 have hvalues : NJB_StateUpdates.add before.1 (batchGroup b) v=ok values := by
  simp only [NJB_StateUpdates.add,av,bind_tc_ok];rfl
 have hweights : NJB_StateUpdates.add before.2 (batchGroup b) w=ok afterWeights := by
  simp only [NJB_StateUpdates.add,aw,bind_tc_ok];rfl
 refine ⟨v,w,values,afterWeights,rv,rw,hvalues,hweights,?_,?_,?_,?_⟩
 · simp only [step,rv,rw,hvalues,hweights,bind_tc_ok]
 · intro i
   dsimp only [values,NJB_StateUpdates.set]
   split <;> first | exact cv' | exact hb.1 i
 · intro i
   dsimp only [afterWeights,NJB_StateUpdates.set]
   split <;> first | exact cw' | exact hb.2 i
 · intro i hi
   simp [values,afterWeights,NJB_StateUpdates.set,Ne.symm hi]

#print axioms canonical_arguments
#print axioms source
end AspisR1.NKR_SumFinishBatch
end
