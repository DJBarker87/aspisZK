import NNU_MerkleLevels
set_option autoImplicit false
namespace AspisR1.NNY_HeightCongruence
open Aeneas Aeneas.Std Result MultiproofConeRef
/-- Abstract height congruence keeps the concrete dictionary out of induction. -/
theorem iterate (left right : reference.Scratch → Result reference.Level)
 (P : reference.Scratch → Prop)
 (step : ∀ s, P s → left s=right s)
 (preserve : ∀ s t, P s → right s=ok (.Done t) → P t)
 (height : Nat) (s : reference.Scratch) (domain : P s) :
 MultiproofConeLevelIteration.iterate left height s =
 MultiproofConeLevelIteration.iterate right height s := by
 induction height generalizing s with
 | zero => rfl
 | succ height ih =>
   simp only [MultiproofConeLevelIteration.iterate,step s domain]
   cases eq : right s with
   | fail e => rfl
   | div => rfl
   | ok out =>
     simp only [bind_tc_ok]
     cases out with
     | Stop stopped => rfl
     | Done after => exact ih after (preserve s after domain eq)
#print axioms iterate
end AspisR1.NNY_HeightCongruence
