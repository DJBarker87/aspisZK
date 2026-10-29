import R1Z.PV_OWN_Operations
set_option autoImplicit false
namespace R1Z.PV_OWN_Unique
open PV_OWN_Heap PV_OWN_Operations
/-- Allocation identity may occur in at most one owning slot. Borrow loans are
not owning slots and do not duplicate the right to drop. -/
def Unique (m : Memory) : Prop :=
 ∀ i j t, m.slots i=some t → m.slots j=some t → i=j

theorem take_preserves (m : Memory) (slot : Nat) (unique:Unique m) : Unique (take slot m) := by
 intro i j t hi hj
 have ni:i≠slot := by intro h; subst i; simp [take] at hi
 have nj:j≠slot := by intro h; subst j; simp [take] at hj
 simp only [take,ni,nj,ite_false] at hi hj
 exact unique i j t hi hj

theorem move_preserves (m : Memory) (src dst : Nat) (t : Token) (c : Cell)
 (unique:Unique m) (source:m.slots src=some t) (empty:m.slots dst=none)
 (distinct:dst≠src) : Unique (move src dst t c m) := by
 intro i j u hi hj
 have ni:i≠src := by intro h; subst i; simp [move] at hi
 have nj:j≠src := by intro h; subst j; simp [move] at hj
 simp only [move,ni,nj,ite_false] at hi hj
 by_cases di:i=dst
 · subst i
   simp only [ite_true] at hi
   cases hi
   by_cases dj:j=dst
   · exact dj.symm
   · simp only [dj,ite_false] at hj
     have eq:=unique j src t hj source
     exact False.elim (nj eq)
 · simp only [di,ite_false] at hi
   by_cases dj:j=dst
   · subst j
     simp only [ite_true] at hj
     cases hj
     have eq:=unique i src t hi source
     exact False.elim (ni eq)
   · simp only [dj,ite_false] at hj
     exact unique i j u hi hj

#print axioms take_preserves
#print axioms move_preserves
end R1Z.PV_OWN_Unique
