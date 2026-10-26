import JFr_RealRounds
set_option autoImplicit false
namespace AspisR1.JFr_NumericContinuity

theorem adjacent (r : Fin 9) :
    JFr_RealRounds.output ⟨r.val,by have := r.isLt;omega⟩=
      JFr_RealRounds.running ⟨r.val+1,by have := r.isLt;omega⟩ := by
  fin_cases r <;> rfl

#print axioms adjacent
end AspisR1.JFr_NumericContinuity
