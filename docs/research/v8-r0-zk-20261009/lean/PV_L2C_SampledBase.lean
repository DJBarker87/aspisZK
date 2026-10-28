import PV_L2C_SamplerFill
import PV_L2C_RouteBaseGuard
set_option autoImplicit false
noncomputable section
namespace PV_L2C_SampledBase
open Aeneas Aeneas.Std Result PV_L2C_M31 PV_L2C_StateSampler
abbrev Cell := PV_L2C_MaskRange.Cell

theorem attached (cells : List Cell) (values : List word)
    (hc : ∀ v ∈ values, canonical v) : ∀ cm ∈ cells.zip values, canonical cm.2 := by
  induction cells generalizing values with
  | nil => simp
  | cons c rest ih =>
    cases values with
    | nil => simp
    | cons v values =>
      intro cm hm
      rcases List.mem_cons.mp hm with he | ht
      · cases he;exact hc v (by simp)
      · exact ih values (by intro v hv;exact hc v (by simp [hv])) cm ht
#print axioms attached

def applySampled {S : Type} (next : S → Result (word × S)) (fuel : Nat)
    (bank : PV_L2C_MaskRange.Bank) (cells : List Cell)
    (active : Fin 1024 → Bool) (dependent : Fin 16 → Usize) : Step S PV_L2C_MaskRange.Bank :=
  bind (PV_L2C_SamplerFill.fill (scalar next fuel) cells.length) (fun values =>
    pure (PV_L2C_MaskRange.balance (PV_L2C_MaskRange.applyCells bank (cells.zip values)) active dependent))

theorem returned {S : Type} (next : S → Result (word × S)) (fuel : Nat)
    (bank : PV_L2C_MaskRange.Bank) (hc : PV_L2C_MaskRange.Canonical bank) (cells : List Cell)
    (active : Fin 1024 → Bool) (dependent : Fin 16 → Usize)
    (s s1 : S) (out : PV_L2C_MaskRange.Bank)
    (h : applySampled next fuel bank cells active dependent s = ok (.ok out,s1)) :
    ∀ c, PV_L2C_BaseGuard.check (PV_L2C_RouteBaseGuard.column out c) = .ok () := by
  unfold applySampled at h
  obtain ⟨values,after,hv,h⟩ := bind_returned _ _ _ _ _ h
  cases h
  obtain ⟨hl,hcan⟩ := PV_L2C_SamplerFill.scalar next cells.length fuel s s1 values hv
  intro c
  exact PV_L2C_RouteBaseGuard.bank_expected _
    (PV_L2C_MaskRange.application bank hc _ (attached cells values hcan) active dependent) c
#print axioms returned
end PV_L2C_SampledBase
