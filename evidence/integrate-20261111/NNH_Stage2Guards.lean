import NNH_Stage2Cut
set_option autoImplicit false
namespace NNH_Stage2Guards
open RSL NND_Returned

theorem value (a : TX2_241.Args)
 (guards : (a.accounts.length != 7 || decide (a.data.length < 4) || a.data.take 4 != REQUEST_MAGIC)=false) :
 a.accounts.length=7 ∧ 4≤a.data.length ∧ a.data.take 4=REQUEST_MAGIC := by
 simp only [Bool.or_eq_false_iff,bne_eq_false_iff_eq,decide_eq_false_iff_not,not_lt] at guards
 exact ⟨guards.1.1,guards.1.2,guards.2⟩
#print axioms value
end NNH_Stage2Guards
