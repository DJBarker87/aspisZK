import NMB_TypedControl
set_option autoImplicit false
namespace NMB_TypedCongr
open Aeneas Aeneas.Std Result AspisR1 NMB_TypedTrace
/-- One source boundary per proof step. Prevents whole-body simplification of
large heterogeneous live environments. No native interpretation is supplied. -/
theorem bind_congr {A B : Type} (m : Run A) (n : NLD_SourceTrace.Trace A)
 (f : A → Run B) (g : A → NLD_SourceTrace.Trace B)
 (head : forget m=n) (tail : ∀ a, forget (f a)=g a) :
 forget (m >>= f)=NJD_Trace.bind n g := by
 rw [forget_bind,head]
 exact legacy_bind_congr n _ g tail
theorem ite_congr {A : Type} (p : Prop) [Decidable p] (a b : Run A)
 (c d : NLD_SourceTrace.Trace A) (yes : p → forget a=c) (no : ¬p → forget b=d) :
 forget (if p then a else b)=(if p then c else d) := by
 by_cases h : p
 · simpa only [if_pos h] using yes h
 · simpa only [if_neg h] using no h
theorem control_congr {A B C : Type} (v : core.ops.control_flow.ControlFlow B C)
 (a : C → Run A) (b : B → Run A)
 (c : C → NLD_SourceTrace.Trace A) (d : B → NLD_SourceTrace.Trace A)
 (yes : ∀ x, forget (a x)=c x) (no : ∀ x, forget (b x)=d x) :
 forget (match v with | .Continue x=>a x | .Break x=>b x)=
 (match v with | .Continue x=>c x | .Break x=>d x) := by
 cases v with
 | Continue x=>exact yes x
 | Break x=>exact no x
#print axioms bind_congr
#print axioms ite_congr
#print axioms control_congr
end NMB_TypedCongr
