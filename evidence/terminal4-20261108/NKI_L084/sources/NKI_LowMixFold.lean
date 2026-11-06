import NKI_LowMix
set_option autoImplicit false
noncomputable section
namespace AspisR1.NKI_LowMixFold
open Aeneas Aeneas.Std Result
open FIv_NativeValue (Canon decode)
open NKI_LowMix (State)
def run (low : Fin 3 → FIv_NativeArithmetic.NQ) (sums : Fin 3 → State) : List (Fin 3) → State → Result State
 | [],before=>ok before
 | g::gs,before=>do let middle←NKI_LowMix.reference before (low g) (sums g);run low sums gs middle
/-- Actual fixed3low-block composition; the one-window native certificate is
instantiated with each previous full2cell poststate and freshly returned cache. -/
theorem source (low : Fin 3 → FIv_NativeArithmetic.NQ) (sums : Fin 3 → State)
 (hl : ∀ g,Canon (low g)) (hs : ∀ g j,Canon (sums g j)) (gs : List (Fin 3)) (before : State) (hb : ∀ j,Canon (before j)) :
 ∃ out,run low sums gs before=ok out ∧ (∀ j,Canon (out j)) ∧
 ∀ j,decode (out j)=decode (before j)+(gs.map (fun g=>decode (low g)*decode (sums g j))).sum := by
 induction gs generalizing before with
 | nil=>exact ⟨before,rfl,hb,by intro j;simp⟩
 | cons g gs ih=>
  obtain ⟨p,cp,cut⟩ := NKI_LowMix.source before (low g) (sums g) hb (hl g) (hs g)
  obtain ⟨out,co,ho,vo⟩ := ih p.out p.canonical
  refine ⟨out,by simp only [run,cp,bind_tc_ok,co],ho,?_⟩
  intro j
  rw [vo,p.values,List.map_cons,List.sum_cons]
  ring
#print axioms source
end AspisR1.NKI_LowMixFold
end
