import NJB_StubLaws
import RPv_JFy_SquareTotal
import RPv_FIw_ScalarArithmetic
set_option autoImplicit false
noncomputable section
namespace AspisR1.NJX_RangeStep
open Aeneas Aeneas.Std Result
open FIv_NativeArithmetic (NQ)
open FIv_NativeValue (Canon decode K)
abbrev State := Fin 33 → NQ
/-- Actual bit residual; multiplication is discharged in Lean, never Kani. -/
def residual (x : NQ) : Result NQ := do
 let square←FIq_Native.field.QM31.square x
 FIq_Native.field.QM31.sub square x

theorem source (x : NQ) (hx : Canon x) :
 ∃ square out,FIq_Native.field.QM31.square x=ok square ∧ residual x=ok out ∧
 Canon out ∧ decode out=decode x*decode x-decode x := by
 obtain ⟨square,sq,hs,vs⟩ := JFy_SquareTotal.source x hx
 obtain ⟨out,co,ho,vo⟩ := NJB_StubLaws.qm_sub square x hs hx
 exact ⟨square,out,sq,by simp only [residual,sq,bind_tc_ok,co],ho,by rw [vo,vs]⟩

def write (s : State) (i : Fin 33) (x : NQ) : State := fun j=>if j=i then x else s j

def index (view : Fin 3) (i : Fin 10) : Fin 33 := ⟨10*view.val+i.val,by have:=view.isLt;have:=i.isLt;omega⟩

def step (view : Fin 3) (i : Fin 10) (x : NQ) (before : State) : Result State := do
 let r←residual x
 ok (write before (index view i) r)
/-- One arbitrary native range-loop prestate, all33cell write frame.
This is233SUPPORT; actual view/control association is still required. -/
theorem step_source (view : Fin 3) (i : Fin 10) (x : NQ) (before : State)
 (hx : Canon x) (hb : ∀ j,Canon (before j)) :
 ∃ out,step view i x before=ok out ∧ (∀ j,Canon (out j)) ∧
 ∀ j,decode (out j)=if j=index view i then decode x*decode x-decode x else decode (before j) := by
 obtain ⟨square,r,sq,cr,hr,vr⟩ := source x hx
 refine ⟨write before (index view i) r,by simp only [step,cr,bind_tc_ok],?_,?_⟩
 · intro j;unfold write;split <;> first|exact hr|exact hb j
 · intro j;unfold write;split <;> simp_all
#print step_source
#print axioms source
#print axioms step_source
end AspisR1.NJX_RangeStep
end
