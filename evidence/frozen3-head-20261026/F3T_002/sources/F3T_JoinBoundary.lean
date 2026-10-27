import F3T_Leaves
set_option autoImplicit false
noncomputable section
namespace AspisR1.F3T_JoinBoundary
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw

/-- Equality of ordered answers follows from log equality and SAME-H acceptance.
This lemma does not manufacture model acceptance from source log equality. -/
theorem accepted_eval (D : LiteralByteProtocol.Decoder) (i : F3_Model.Input)
    (source : Program Bytes State Bool) (H : Bytes → State)
    (sourceAccepted : (eval H source).2=true)
    (modelAccepted : (eval H (F3_Model.verifier D i)).2=true)
    (logs : (eval H source).1=(eval H (F3_Model.verifier D i)).1) :
    eval H source=eval H (F3_Model.verifier D i) := by
  exact Prod.ext logs (sourceAccepted.trans modelAccepted.symm)

/-- The exact collision exception is preserved. In particular, an all-H strict
raw join is not obtained by silently dropping the left alternatives. -/
theorem collision_or_eval (D : LiteralByteProtocol.Decoder) (i : F3_Model.Input)
    (source : Program Bytes State Bool) (H : Bytes → State) (collision : Prop)
    (sourceAccepted : (eval H source).2=true)
    (accepted : collision ∨ (eval H (F3_Model.verifier D i)).2=true)
    (logs : collision ∨ (eval H source).1=(eval H (F3_Model.verifier D i)).1) :
    collision ∨ eval H source=eval H (F3_Model.verifier D i) := by
  rcases accepted with bad | yes
  · exact Or.inl bad
  rcases logs with bad | equal
  · exact Or.inl bad
  · exact Or.inr (accepted_eval D i source H sourceAccepted yes equal)

/-- Pure logical obstruction only, NOT an installed-source counterexample. -/
theorem dropping_collision_invalid :
    ¬ (∀ (collision equal : Prop), (collision ∨ equal) → equal) := by
  intro dropped
  exact dropped True False (Or.inl trivial)

#print axioms accepted_eval
#print axioms collision_or_eval
#print axioms dropping_collision_invalid
end AspisR1.F3T_JoinBoundary
end
