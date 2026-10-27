import R1Z.PV_Inv_GlobalSlots
set_option autoImplicit false
namespace R1Z.PV_Inv_GlobalSafety
open PV_Inv_RawSlots PV_Inv_GlobalSlots
variable {I V W : Type} [DecidableEq I] [Zero W] [DecidableEq W]

theorem run_good (P : I → V → Prop) (s t : State I V W) (es : List (I × Entry V W))
    (hs : PV_Inv_GlobalSlots.Good P s) (hp : ∀ e ∈ es, P e.1 e.2.value)
    (hr : PV_Inv_GlobalSlots.run s es=some t) : PV_Inv_GlobalSlots.Good P t := by
  induction es generalizing s with
  | nil => cases hr; exact hs
  | cons e es ih =>
    simp only [PV_Inv_GlobalSlots.run] at hr
    cases he : PV_Inv_GlobalSlots.step s e with
    | none => simp [he] at hr
    | some u =>
      simp only [he,Option.bind_some] at hr
      apply ih u (PV_Inv_GlobalSlots.step_good P s u e hs (hp e (by simp)) he)
      · intro e' he'
        exact hp e' (by simp [he'])
      · exact hr

def empty (z : V) : State I V W := fun _ => PV_Inv_RawRun.empty z

theorem empty_good (z : V) (P : I → V → Prop) : PV_Inv_GlobalSlots.Good P (empty z : State I V W) :=
  fun i => PV_Inv_RawRun.empty_good (P i) z

#print axioms run_good
#print axioms empty_good
end R1Z.PV_Inv_GlobalSafety
