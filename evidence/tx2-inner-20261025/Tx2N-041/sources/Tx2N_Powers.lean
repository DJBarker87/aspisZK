import LoopPowersEarlyTotal
import VTop_Provenance
set_option autoImplicit false
noncomputable section
namespace AspisR1.Tx2N_Powers
open Aeneas Aeneas.Std Result
abbrev E := VTop_Stages.aspis_core.field.wide_exact.WideExact
abbrev PE := AspisR1LoopPowers.field.WideExact

def toCM (x : VTop_Stages.aspis_core.field.CM31) : AspisR1LoopPowers.field.CM31 := ⟨x.a,x.b⟩
def toQM (x : VTop_Stages.aspis_core.field.QM31) : AspisR1LoopPowers.field.QM31 := ⟨toCM x.c0,toCM x.c1⟩
def toPowers (x : E) : PE := ⟨toQM x.c0,toQM x.c1⟩
def fromCM (x : AspisR1LoopPowers.field.CM31) : VTop_Stages.aspis_core.field.CM31 := ⟨x.a,x.b⟩
def fromQM (x : AspisR1LoopPowers.field.QM31) : VTop_Stages.aspis_core.field.QM31 := ⟨fromCM x.c0,fromCM x.c1⟩
def fromPowers (x : PE) : E := ⟨fromQM x.c0,fromQM x.c1⟩
def mapArray {N : Usize} (out : Array PE N) : Array E N :=
  ⟨out.val.map fromPowers,by simpa only [List.length_map] using out.property⟩

def powers (N : Usize) (x : E) : Result (Array E N) := do
  let out ← AspisR1LoopPowers.weights.early_powers N (toPowers x)
  ok (mapArray out)

theorem roundtrip (x : PE) : toPowers (fromPowers x) = x := by
  cases x with | mk c0 c1 => cases c0; cases c1; rfl

/-- The existing named Session A instance, transported only across nominal
field records. No new powers hypothesis is introduced. -/
theorem total_exact (N : Usize) (x : E) (canonical : AspisR1LoopPowers.Canonical (toPowers x)) :
    ∃ out, powers N x = ok out ∧ ∀ j : Fin N.val,
      AspisR1LoopPowers.Canonical (toPowers (out.val[j.val]'(by rw [out.property]; exact j.isLt))) ∧
      AspisR1LoopPowers.decode (toPowers (out.val[j.val]'(by rw [out.property]; exact j.isLt))) =
        AspisR1LoopPowers.decode (toPowers x)^j.val := by
  obtain ⟨out,call,values⟩ := AspisR1LoopPowers.early_powers_total_exact N (toPowers x) canonical
  refine ⟨mapArray out,?_,?_⟩
  · simp only [powers,call,bind_tc_ok]
  · intro j
    simpa only [mapArray,List.getElem_map,roundtrip] using values j

#print axioms roundtrip
#print axioms total_exact
end AspisR1.Tx2N_Powers
end
