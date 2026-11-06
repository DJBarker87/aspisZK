import NJL_PathContext
import NJL_WriteFrame
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_PathStep
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJL_PathContext (Context Domain State)
def weight (c : Context) (right : Bool) : NQ := if right then c.selected else c.emptyValue
def cache (c : Context) (right : Bool) : FIv_PreparedNew.NP := if right then c.right else c.left
def sourceIndex (right : Bool) (k : Fin 8) : Fin 16 := ⟨(if right then 8 else 0)+k.val,by cases right <;> simp_all <;> omega⟩
def currentIndex (k : Fin 8) : Fin 16 := ⟨k.val+1,by omega⟩
def target (right : Bool) (k : Fin 8) : Fin 17 := ⟨(if right then 9 else 1)+k.val,by cases right <;> simp_all <;> omega⟩
def reference (c : Context) (z succ : Fin 16 → NQ) (right : Bool) (k : Fin 8) (before : State) : Result State := do
 let difference ← FIq_Native.field.QM31.sub (succ (sourceIndex right k)) (z (currentIndex k))
 let reply ← FIq_Native.field.PreparedQm31Multiplier.mul (cache c right) difference
 ok (NJB_StateUpdates.set before (target right k) reply)
/-- NJB_path_one_side native2-call window. Right-side domains k<7 and k=7
are disjoint/exhaustive; left covers all k<8. Full17-cell frame observed. -/
def Cut (c : Context) (z succ : Fin 16 → NQ) (right : Bool) (k : Fin 8) (before after : State)
 (difference reply : NQ) (events : Fin 2 → NJB_Cuts.Event) (seen : FIv_PreparedNew.NP) (calls : Nat) : Prop :=
 calls=2 ∧ (events 0).operation=2 ∧ (events 1).operation=4 ∧
 (events 0).left=succ (sourceIndex right k) ∧ (events 0).right=z (currentIndex k) ∧
 seen=cache c right ∧ (events 1).right=difference ∧
 ∀ i,after i=if i=target right k then reply else before i
def Step (c : Context) (z succ : Fin 16 → NQ) (right : Bool) (k : Fin 8) (before after : State) : Prop :=
 ∃ difference reply events,
 FIq_Native.field.QM31.sub (succ (sourceIndex right k)) (z (currentIndex k))=ok difference ∧
 FIq_Native.field.PreparedQm31Multiplier.mul (cache c right) difference=ok reply ∧
 Cut c z succ right k before after difference reply events (cache c right) 2
def modelStep (c : Context) (z succ : Fin 16 → NQ) (right : Bool) (k : Fin 8) (before : Fin 17 → K) : Fin 17 → K :=
 NJL_WriteFrame.write before (target right k) (decode (weight c right)*(decode (succ (sourceIndex right k))-decode (z (currentIndex k))))
theorem domain (c : Context) (right : Bool) (hc : Domain c) :
 Canon (weight c right) ∧ NJB_PreparedLaws.Domain (cache c right) (weight c right) := by
 cases right
 · exact ⟨hc.2.1,hc.2.2.2.1⟩
 · exact ⟨hc.1,hc.2.2.2.2⟩
theorem source (c : Context) (z succ : Fin 16 → NQ) (right : Bool) (k : Fin 8) (before : State)
 (hc : Domain c) (hz : ∀ i,Canon (z i)) (hs : ∀ i,Canon (succ i)) (hb : ∀ i,Canon (before i)) :
 ∃ after,reference c z succ right k before=ok after ∧ Step c z succ right k before after ∧
 (∀ i,Canon (after i)) ∧ (fun i=>decode (after i))=modelStep c z succ right k (fun i=>decode (before i)) := by
 obtain ⟨difference,cd,hd,vd⟩ := NJB_StubLaws.qm_sub (succ (sourceIndex right k)) (z (currentIndex k)) (hs _) (hz _)
 have dm := domain c right hc
 obtain ⟨reply,cr,hr,vr⟩ := NJB_PreparedLaws.mul_result (cache c right) (weight c right) difference dm.1 hd dm.2
 let after := NJB_StateUpdates.set before (target right k) reply
 let events : Fin 2 → NJB_Cuts.Event := ![⟨2,succ (sourceIndex right k),z (currentIndex k)⟩,⟨4,FIq_Native.field.QM31.ZERO,difference⟩]
 refine ⟨after,?_,⟨difference,reply,events,cd,cr,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩,?_,?_⟩
 · simp only [reference,cd,cr,bind_tc_ok];rfl
 · intro i
   simp only [after,NJB_StateUpdates.set,eq_comm]
 · intro i
   dsimp only [after,NJB_StateUpdates.set]
   split <;> first | exact hr | exact hb i
 · funext i
   by_cases same : target right k=i
   · simp [after,NJB_StateUpdates.set,modelStep,NJL_WriteFrame.write,same,vr,vd]
   · simp [after,NJB_StateUpdates.set,modelStep,NJL_WriteFrame.write,same]
#print axioms domain
#print axioms source
end AspisR1.NJL_PathStep
end
