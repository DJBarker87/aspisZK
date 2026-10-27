import R1Z.PV_Inv_RawSlots
set_option autoImplicit false
namespace R1Z.PV_Inv_RawMap
open PV_Inv_RawSlots
variable {V U W : Type} [Zero W] [DecidableEq W]

def entry (f : V → U) (e : Entry V W) : Entry U W := ⟨f e.value,e.weight⟩
def slots (f : V → U) (s : Slots V W) : Slots U W := fun i => entry f (s i)

theorem put_map (f : V → U) (s : Slots V W) (i : Fin 2) (e : Entry V W) :
    slots f (put s i e) = put (slots f s) i (entry f e) := by
  funext j
  by_cases h : j=i <;> simp [slots,put,h]

theorem step_map (f : V → U) (s : Slots V W) (e : Entry V W) :
    step (slots f s) (entry f e) = (step s e).map (slots f) := by
  unfold step
  simp only [slots,entry]
  split <;> split <;> simp_all [put_map]

#print axioms put_map
#print axioms step_map
end R1Z.PV_Inv_RawMap
