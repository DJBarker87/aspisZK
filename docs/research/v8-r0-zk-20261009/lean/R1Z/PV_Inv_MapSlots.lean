import R1Z.PV_Inv_RawSlots
set_option autoImplicit false
namespace R1Z.PV_Inv_MapSlots
open PV_Inv_RawSlots
variable {V V' W : Type} [Zero W] [DecidableEq W]

def entry (f : V → V') (e : Entry V W) : Entry V' W := ⟨f e.value,e.weight⟩
def slots (f : V → V') (s : Slots V W) : Slots V' W := fun i => entry f (s i)

theorem put_map (f : V → V') (s : Slots V W) (i : Fin 2) (e : Entry V W) :
    slots f (put s i e) = put (slots f s) i (entry f e) := by
  funext j
  by_cases h : j=i
  · subst j; simp [slots,put]
  · simp [slots,put,h]

theorem step_map (f : V → V') (s : Slots V W) (e : Entry V W) :
    PV_Inv_RawSlots.step (slots f s) (entry f e) =
      (PV_Inv_RawSlots.step s e).map (slots f) := by
  unfold PV_Inv_RawSlots.step
  change (if (s 0).weight=0 then some _ else if (s 1).weight=0 then some _ else none) = _
  by_cases h0 : (s 0).weight=0 <;> by_cases h1 : (s 1).weight=0 <;>
    simp only [h0,h1,↓reduceIte,Option.map_some,Option.map_none,put_map]

#print axioms put_map
#print axioms step_map
end R1Z.PV_Inv_MapSlots
