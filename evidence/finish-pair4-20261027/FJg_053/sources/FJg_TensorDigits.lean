import FJd_PointReference
set_option autoImplicit false
namespace AspisR1.FJg_TensorDigits

def index (i : Fin 64) (s t : Fin 4) : Fin 1024 :=
  ⟨16*i.val+4*s.val+t.val,by have := i.isLt;have := s.isLt;have := t.isLt;omega⟩

theorem zero (i : Fin 64) (s t : Fin 4) : (index i s t).val%4=t.val := by
  dsimp only [index]
  have := s.isLt;have := t.isLt;omega

theorem one (i : Fin 64) (s t : Fin 4) : (index i s t).val/4%4=s.val := by
  dsimp only [index]
  have := s.isLt;have := t.isLt;omega

theorem two (i : Fin 64) (s t : Fin 4) : (index i s t).val/16%4=i.val%4 := by
  dsimp only [index]
  have := s.isLt;have := t.isLt;omega

theorem three (i : Fin 64) (s t : Fin 4) : (index i s t).val/64%4=i.val/4%4 := by
  dsimp only [index]
  have := s.isLt;have := t.isLt;omega

theorem four (i : Fin 64) (s t : Fin 4) : (index i s t).val/256%4=i.val/16 := by
  dsimp only [index]
  have := i.isLt;have := s.isLt;have := t.isLt;omega
#print axioms zero
#print axioms one
#print axioms two
#print axioms three
#print axioms four
end AspisR1.FJg_TensorDigits
