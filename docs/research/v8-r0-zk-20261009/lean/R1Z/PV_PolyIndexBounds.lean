import Std
set_option autoImplicit false
namespace R1Z.PV_PolyIndexBounds

theorem coefficient (block offset : Nat) (hb : block < 7) (ho : offset < 4) :
    4*block+offset < 28 := by omega

theorem predecessor (block : Nat) (positive : 0 < block) : block-1 < block := by omega

theorem next_block (block : Nat) (positive : 0 < block) (bound : block ≤ 6) :
    block-1 < 7 := by omega

theorem initial_block : 4*6+3 < 28 := by decide

theorem prepared_component (i : Nat) (bound : i<3) : i < 3 := bound

#print axioms coefficient
#print axioms predecessor
#print axioms next_block
#print axioms initial_block
#print axioms prepared_component
end R1Z.PV_PolyIndexBounds
