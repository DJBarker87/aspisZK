import R1Z.PV_Inv_GlobalSlots
set_option autoImplicit false
namespace R1Z.PV_Inv_GlobalProjection
open PV_Inv_RawSlots PV_Inv_GlobalSlots
variable {I V W : Type} [DecidableEq I] [Zero W] [DecidableEq W]

theorem target (s : State I V W) (e : I × Entry V W) :
    (PV_Inv_GlobalSlots.step s e).map (fun t => t e.1)=PV_Inv_RawSlots.step (s e.1) e.2 := by
  unfold PV_Inv_GlobalSlots.step
  cases h : PV_Inv_RawSlots.step (s e.1) e.2 <;> simp [h]

theorem other (s t : State I V W) (e : I × Entry V W) (i : I)
    (hi : i ≠ e.1) (hr : PV_Inv_GlobalSlots.step s e=some t) : t i=s i := by
  unfold PV_Inv_GlobalSlots.step at hr
  cases h : PV_Inv_RawSlots.step (s e.1) e.2 with
  | none => simp [h] at hr
  | some u =>
    simp only [h,Option.map_some,Option.some.injEq] at hr
    subst t
    simp [hi]

#print axioms target
#print axioms other
end R1Z.PV_Inv_GlobalProjection
