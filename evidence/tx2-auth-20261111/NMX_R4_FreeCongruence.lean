import NMX_R4_CallProgram
set_option autoImplicit false
namespace NMX_R4_FreeCongruence
open NMX_R4_CallProgram
/-- Preserve the free call itself; inspect only the arbitrary reply in its
continuation. Generated matchers are compared by constructors, not unfolding. -/
theorem step {A B : Type} (p : Program A) (f g : A → Program B) (h : ∀ a, f a = g a) :
 NMX_R4_CallProgram.bind p f = NMX_R4_CallProgram.bind p g :=
 congrArg (NMX_R4_CallProgram.bind p) (funext h)
#print axioms step
end NMX_R4_FreeCongruence
