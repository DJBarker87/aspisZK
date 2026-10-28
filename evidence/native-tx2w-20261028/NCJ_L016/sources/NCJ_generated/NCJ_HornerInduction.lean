import NBG_WideCarriers
import NCJ_CallLog
set_option autoImplicit false
noncomputable section
namespace NCJ_HornerInduction
open Aeneas Aeneas.Std Result AspisR1 LPi_FieldValues
abbrev E := NE

def addE (x y : EW) : EW := (addQ x.1 y.1,addQ x.2 y.2)

def step (a x c : E) : Result E := do
  let product ← FIo_Native.aspis_core.field.wide_exact.WideExact.mul a x
  FIo_Native.aspis_core.field.wide_exact.WideExact.add product c

def go (x : E) : List E → E → Result E
  | [],a => ok a
  | c::cs,a => do
    let next ← step a x c
    go x cs next

theorem step_total (a x c : E) (ha : canonE a) (hx : canonE x) (hc : canonE c) :
    ∃ z,step a x c=ok z ∧ canonE z ∧ ew z=addE (mulE (ew a) (ew x)) (ew c) := by
  obtain ⟨p,hp,cp,vp⟩ := LPi_TowerValues.wide_mul a x ha hx
  obtain ⟨z,hz,cz,vz⟩ := NBG_WideCarriers.wide_add p c cp hc
  refine ⟨z,?_,cz,?_⟩
  · simp only [step,hp,hz,bind_tc_ok]
  · simpa only [addE,ew,vp] using vz

/-- One arbitrary native Horner step plus induction; no seven-step native
unwind and no native multiplication is required. Decoder association remains
an explicit caller obligation on the same coefficient sequence. -/
theorem total (x a : E) (hx : canonE x) (ha : canonE a) (cs : List E)
    (hc : ∀ c∈cs,canonE c) :
    ∃ out,go x cs a=ok out ∧ canonE out ∧
      ew out=cs.foldl (fun v c=>addE (mulE v (ew x)) (ew c)) (ew a) := by
  induction cs generalizing a with
  | nil => exact ⟨a,rfl,ha,rfl⟩
  | cons c cs ih =>
    obtain ⟨next,run,canonical,value⟩ := step_total a x c ha hx (hc c (by simp))
    obtain ⟨out,tail,co,vo⟩ := ih next canonical (fun t ht=>hc t (by simp [ht]))
    refine ⟨out,?_,co,?_⟩
    · simp only [go,run,tail,bind_tc_ok]
    · simpa only [List.foldl_cons,value] using vo

#print axioms step_total
#print axioms total
end NCJ_HornerInduction
