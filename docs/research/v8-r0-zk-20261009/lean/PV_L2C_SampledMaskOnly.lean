import PV_L2C_SamplerFill
import PV_L2C_RouteBaseGuard
set_option autoImplicit false
namespace PV_L2C_SampledMaskOnly
open Aeneas Aeneas.Std Result PV_L2C_M31 PV_L2C_StateSampler

def table (values : List word) : Fin 1024 → word := fun r => values[r.val]!

theorem sampled {S : Type} (next : S → Result (word × S)) (fuel : Nat)
    (s s1 : S) (values : List word)
    (h : PV_L2C_SamplerFill.fill (scalar next fuel) 1024 s = ok (.ok values,s1)) :
    ∀ r, canonical (table values r) := by
  obtain ⟨hl,hc⟩ := PV_L2C_SamplerFill.scalar next 1024 fuel s s1 values h
  intro r
  have hr : r.val < values.length := by rw [hl];exact r.isLt
  apply hc
  rw [table,getElem!_pos values r.val hr]
  exact List.getElem_mem hr
#print axioms sampled

def balanced (values : List word) (active : Fin 1024 → Bool) (dependent : Usize) :=
  PV_L2C_ScalarBalance.output (table values) active dependent

theorem guard {S : Type} (next : S → Result (word × S)) (fuel : Nat)
    (s s1 : S) (values : List word)
    (h : PV_L2C_SamplerFill.fill (scalar next fuel) 1024 s = ok (.ok values,s1))
    (active : Fin 1024 → Bool) (dependent : Usize) :
    PV_L2C_BaseGuard.check (List.ofFn (fun r : Fin 1024 => (⟨balanced values active dependent r⟩ : U32))) = .ok () := by
  apply PV_L2C_BaseGuard.expected
  · simp only [List.length_ofFn]
  · intro j hj
    rw [List.getElem!_eq_getElem?_getD,List.getElem?_ofFn,dif_pos hj]
    exact PV_L2C_ScalarCanonical.output_canonical _ active
      (sampled next fuel s s1 values h) dependent ⟨j,hj⟩
#print axioms guard
end PV_L2C_SampledMaskOnly
