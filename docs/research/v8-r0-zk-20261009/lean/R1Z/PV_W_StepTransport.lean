import R1Z.PV_W_Threading
set_option autoImplicit false
namespace R1Z.PV_W_StepTransport
open PV_W_Threading
variable {W C E A : Type}

theorem threaded_mono (small large : W → C → W → Prop)
    (embedStep : ∀ w c n, small w c n → large w c n)
    {w n : W} {calls : List (W × C)} (h : Threaded small w calls n) :
    Threaded large w calls n := by
  induction h with
  | nil w => exact .nil w
  | cons first rest ih => exact .cons (embedStep _ _ _ first) ih

theorem valid_mono (small large : W → C → W → Prop)
    (embedStep : ∀ w c n, small w c n → large w c n)
    (m : M W C E A) (h : Valid small m) : Valid large m :=
  fun w => threaded_mono small large embedStep (h w)

#print axioms threaded_mono
#print axioms valid_mono
end R1Z.PV_W_StepTransport
