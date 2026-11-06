import NJX_RangeStep
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_RangeFold
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
open NJX_RangeStep (State index)
def modelStep (view : Fin 3) (xs : Fin 10 → NQ) (i : Fin 10) (s : Fin 33 → K) : Fin 33 → K :=
 Function.update s (index view i) (decode (xs i)*decode (xs i)-decode (xs i))
def run (view : Fin 3) (xs : Fin 10 → NQ) : List (Fin 10) → State → Result State
 | [],s=>ok s
 | i::is,s=>do
   let next←NJX_RangeStep.step view i (xs i) s
   run view xs is next
inductive Trace (view : Fin 3) (xs : Fin 10 → NQ) : List (Fin 10) → State → State → Prop
 | nil (s) : Trace view xs [] s s
 | cons {i is before middle after} : NJX_RangeStep.step view i (xs i) before=ok middle →
   (∀ j,middle j=if j=index view i then middle (index view i) else before j) →
   Trace view xs is middle after → Trace view xs (i::is) before after
/-- One arbitrary-prestate step followed by finite10iteration induction;
all33cell frames and canonical intermediate square/sub domains retained. -/
theorem source (view : Fin 3) (xs : Fin 10 → NQ) (hx : ∀ i,Canon (xs i))
 (is : List (Fin 10)) (before : State) (hb : ∀ j,Canon (before j)) :
 ∃ out,run view xs is before=ok out ∧ Trace view xs is before out ∧
 (∀ j,Canon (out j)) ∧ (fun j=>decode (out j))=is.foldl (fun s i=>modelStep view xs i s) (fun j=>decode (before j)) := by
 induction is generalizing before with
 | nil=>exact ⟨before,rfl,.nil before,hb,rfl⟩
 | cons i is ih=>
  obtain ⟨square,r,cs,cr,hr,vr⟩ := NJX_RangeStep.source (xs i) (hx i)
  let middle:=NJX_RangeStep.write before (index view i) r
  have cm : NJX_RangeStep.step view i (xs i) before=ok middle := by simp only [NJX_RangeStep.step,cr,bind_tc_ok];rfl
  have hm : ∀ j,Canon (middle j) := by intro j;dsimp [middle,NJX_RangeStep.write];split <;> first|exact hr|exact hb j
  obtain ⟨out,co,tr,ho,vo⟩ := ih middle hm
  refine ⟨out,by simp only [run,cm,bind_tc_ok,co],.cons cm ?_ tr,ho,?_⟩
  · intro j
    dsimp [middle,NJX_RangeStep.write]
    by_cases h:j=index view i <;> simp [h]
  · rw [vo,List.foldl_cons]
    congr 1
    funext j
    simp only [middle,NJX_RangeStep.write,modelStep,Function.update_apply]
    split <;> simp_all
#print source
#print axioms source
end AspisR1.NJX_RangeFold
end
