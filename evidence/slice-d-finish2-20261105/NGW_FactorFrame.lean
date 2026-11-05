import KMX_CopyMeaning
set_option autoImplicit false
namespace NGW_FactorFrame

def start (k d : Nat) : Nat := 4*(5*k+d)

theorem disjoint (k d kind dim term : Nat) (hd : d<5) (hm : dim<5) (ht : term<4)
 (other : ¬(kind=k ∧ dim=d)) :
 start kind dim+term<start k d ∨ start k d+4≤start kind dim+term := by
 unfold start
 have ne : 5*kind+dim ≠ 5*k+d := by
  intro same
  apply other
  constructor <;> omega
 omega

theorem copied {α : Type} (src dst : Nat → α) (k d term : Nat) (ht : term<4) :
 KMX_CopyMeaning.loop src dst (start k d) 4 (start k d+term)=src (start k d+term) := by
 rw [KMX_CopyMeaning.loop_spec,if_pos (by omega)]

theorem frame {α : Type} (src dst : Nat → α) (k d kind dim term : Nat)
 (hd : d<5) (hm : dim<5) (ht : term<4) (other : ¬(kind=k ∧ dim=d)) :
 KMX_CopyMeaning.loop src dst (start k d) 4 (start kind dim+term)=dst (start kind dim+term) :=
 KMX_CopyMeaning.copy_frame src dst _ _ _ (disjoint k d kind dim term hd hm ht other)

#print axioms disjoint
#print axioms copied
#print axioms frame
end NGW_FactorFrame
