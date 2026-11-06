import NJL_OccupancyContext
import NJL_OccupancyHead
import RPv_FIw_ScalarArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJL_OccupancyTail
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJL_OccupancyHead (State)
def reference (before : State) (input output occupied ten oneMinus : NQ) (expected : U32) : Result State := do
 let r0 ← FIq_Native.field.QM31.mul ten oneMinus
 let r1 ← FIq_Native.field.QM31.mul input r0
 let lifted ← FIq_Native.pool_v1.pair_forest_semantic_terminal.lift_m31 expected
 let r2 ← FIq_Native.field.QM31.sub occupied lifted
 let r3 ← FIq_Native.field.QM31.mul output r2
 let r4 ← FIq_Native.field.QM31.add r1 r3
 ok (fun i=>if i.val=11 then r4 else before i)
def Clauses (input output occupied ten oneMinus : NQ) (expected : U32) (r : Fin 5 → NQ) : Prop :=
 FIq_Native.field.QM31.mul ten oneMinus=ok (r 0) ∧
 FIq_Native.field.QM31.mul input (r 0)=ok (r 1) ∧
 FIq_Native.pool_v1.pair_forest_semantic_terminal.lift_m31 expected=ok (FIw_ScalarArithmetic.lifted expected) ∧
 FIq_Native.field.QM31.sub occupied (FIw_ScalarArithmetic.lifted expected)=ok (r 2) ∧
 FIq_Native.field.QM31.mul output (r 2)=ok (r 3) ∧
 FIq_Native.field.QM31.add (r 1) (r 3)=ok (r 4)
/-- NJB_K090/K091: exact five-call tail and complete12-cell frame. The lift
executes natively and its full emitted Result is discharged from the pinned law. -/
def Cut (before after : State) (input output occupied ten oneMinus : NQ) (expected : U32)
 (r : Fin 5 → NQ) (events : Fin 5 → NJB_Cuts.Event) (calls : Nat) : Prop :=
 calls=5 ∧
 (∀ j,(events j).operation=(![0,0,2,0,1] : Fin 5 → Nat) j ∧
  (events j).left=(![ten,input,occupied,output,r 1] : Fin 5 → NQ) j ∧
  (events j).right=(![oneMinus,r 0,FIw_ScalarArithmetic.lifted expected,r 2,r 3] : Fin 5 → NQ) j) ∧
 ∀ i,after i=if i.val=11 then r 4 else before i
theorem source (before : State) (input output occupied ten oneMinus : NQ) (expected : U32)
 (hb : ∀ i,Canon (before i)) (hi : Canon input) (ho : Canon output) (hc : Canon occupied)
 (ht : Canon ten) (hm : Canon oneMinus) (he : expected.val<FIw_ScalarArithmetic.P) :
 ∃ r after events,reference before input output occupied ten oneMinus expected=ok after ∧
 Clauses input output occupied ten oneMinus expected r ∧ Cut before after input output occupied ten oneMinus expected r events 5 ∧
 (∀ i,Canon (after i)) ∧ (∀ i,decode (after i)=if i.val=11 then
  decode input*(decode ten*decode oneMinus)+decode output*(decode occupied-(expected.val : K)) else decode (before i)) := by
 obtain ⟨r0,h0,c0,v0⟩ := NJB_StubLaws.qm_mul ten oneMinus ht hm
 obtain ⟨r1,h1,c1,v1⟩ := NJB_StubLaws.qm_mul input r0 hi c0
 have lift := FIw_ScalarArithmetic.lift_run expected
 have lv := FIw_ScalarArithmetic.lift_value expected he
 obtain ⟨r2,h2,c2,v2⟩ := NJB_StubLaws.qm_sub occupied (FIw_ScalarArithmetic.lifted expected) hc lv.1
 obtain ⟨r3,h3,c3,v3⟩ := NJB_StubLaws.qm_mul output r2 ho c2
 obtain ⟨r4,h4,c4,v4⟩ := NJB_StubLaws.qm_add r1 r3 c1 c3
 let r : Fin 5 → NQ := ![r0,r1,r2,r3,r4]
 let after : State := fun i=>if i.val=11 then r4 else before i
 let events : Fin 5 → NJB_Cuts.Event := fun j=>
  ⟨(![0,0,2,0,1] : Fin 5 → Nat) j,
   (![ten,input,occupied,output,r1] : Fin 5 → NQ) j,
   (![oneMinus,r0,FIw_ScalarArithmetic.lifted expected,r2,r3] : Fin 5 → NQ) j⟩
 refine ⟨r,after,events,?_,⟨h0,h1,lift,h2,h3,h4⟩,?_,?_,?_⟩
 · simp only [reference,h0,h1,lift,h2,h3,h4,bind_tc_ok];rfl
 · exact ⟨rfl,by intro j;fin_cases j <;> exact ⟨rfl,rfl,rfl⟩,fun _=>rfl⟩
 · intro i
   dsimp only [after]
   split <;> first | exact c4 | exact hb i
 · intro i
   by_cases same : i.val=11
   · simp [after,same,v4,v1,v0,v3,v2,lv.2]
   · simp [after,same]
#print axioms source
end AspisR1.NJL_OccupancyTail
end
