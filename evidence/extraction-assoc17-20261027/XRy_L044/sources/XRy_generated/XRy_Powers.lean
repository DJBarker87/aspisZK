import XRy_PowersLoop
open Aeneas Aeneas.Std Result
open XRo_Join_Carriers XRn_Join_FieldExternal XRy_LoopWide
set_option autoImplicit false
namespace XRy_Powers

def zero : C.E := ⟨oldQ qzero,oldQ qzero⟩
def one : C.E := ⟨oldQ qone,oldQ qzero⟩

theorem one_canonical : XRy_WideMultiply.Canonical one := by
 constructor <;> constructor <;> constructor <;> (change _ < 2147483647; decide)

theorem zero_loop : toLoop zero = AspisR1LoopPowers.field.WideExact.ZERO := by
 unfold AspisR1LoopPowers.field.WideExact.ZERO AspisR1LoopPowers.field.QM31.ZERO
 rfl

theorem one_loop : toLoop one = AspisR1LoopPowers.field.WideExact.ONE := by
 unfold AspisR1LoopPowers.field.WideExact.ONE AspisR1LoopPowers.field.QM31.ONE
   AspisR1LoopPowers.field.QM31.ZERO
 rfl

theorem paired (N : Usize) (x : C.E) (hx : XRy_WideMultiply.Canonical x) :
 ∃ out, XRn_Join_Release.weights.powers N x = ok out ∧
 AspisR1LoopPowers.weights.early_powers N (toLoop x) = ok (arr toLoop out) := by
 obtain ⟨out,pending,hr,hp,ht⟩ := XRy_PowersLoop.paired N.val x hx
   (Array.repeat N zero) one one_canonical 0#usize (by scalar_tac) (by scalar_tac)
 refine ⟨out,?_,?_⟩
 · unfold XRn_Join_Release.weights.powers
   simp only [aspis_core.field.wide_exact.WideExact.ZERO,
     aspis_core.field.wide_exact.WideExact.ONE,bind_tc_ok]
   change (do let (out,pending) ← XRn_Join_Release.weights.powers_loop x (Array.repeat N zero) one 0#usize
              match pending with | none => ok out | some out2 => ok out2) = ok out
   rw [hr,bind_tc_ok]
   rcases hp with hp | hp <;> rw [hp]
 · simpa only [AspisR1LoopPowers.weights.early_powers,XRy_ArrayMap.repeated,zero_loop,one_loop] using ht

#print axioms one_canonical
#print axioms zero_loop
#print axioms one_loop
#print axioms paired
end XRy_Powers
