import PoolV_ChronologyAccepted
set_option autoImplicit false
namespace AspisR1.PoolS2_ChronologyCodes
open Aeneas Aeneas.Std Result PoolV_ChronologyFacts

theorem codes (new old : Slice U64) (has : Bool) (seq : U64) (pair : U8 × U64)
    (h : PoolV_Chronology.chronology new old has seq = ok pair) :
    pair.1 = 0#u8 ∨ pair.1 = 1#u8 ∨ pair.1 = 2#u8 ∨ pair.1 = 3#u8 := by
  rw [total] at h
  have same := Result.ok.inj h
  subst pair
  cases has <;> cases hd : decreased new old <;> cases hp : progressed new old <;>
    by_cases hs : seq = core.num.U64.MAX <;> simp [specification,hd,hp,hs]

theorem accepted_code (new old : Slice U64) (has : Bool) (seq : U64) (pair : U8 × U64)
    (h : PoolV_Chronology.chronology new old has seq = ok pair)
    (a : pair.1 ≠ 1#u8) (b : pair.1 ≠ 2#u8) (c : pair.1 ≠ 3#u8) :
    pair.1 = 0#u8 := by
  rcases codes new old has seq pair h with h | h | h | h
  · exact h
  · exact False.elim (a h)
  · exact False.elim (b h)
  · exact False.elim (c h)

#print axioms codes
#print axioms accepted_code
end AspisR1.PoolS2_ChronologyCodes
