import NFW_Bind
set_option autoImplicit false
namespace AspisR1.NFW_Invert
open Aeneas Aeneas.Std Result
theorem bind {A B : Type} (m : Result A) (f : A→Result B) (out : B)
 (run : (do let x←m;f x)=ok out) : ∃ x,m=ok x ∧ f x=ok out := by
 cases m with
 | ok x => exact ⟨x,rfl,run⟩
 | fail err => simp only [bind_tc_fail] at run;cases run
 | div => simp only [bind_tc_div] at run;cases run
#print axioms bind
end AspisR1.NFW_Invert
