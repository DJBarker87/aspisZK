import NMP_ObservedSuffix0
set_option autoImplicit false
noncomputable section
namespace AspisR1.NMP_ObservedSuffix
open Aeneas Aeneas.Std Result NMP_prepare NMP_Emitted
/-- Frozen emission and the six-call normal form have exactly the same full
Result. No successful child, native endpoint or strengthened input premise. -/
theorem source {H W : Type} (c : Calls) (s : Parent H W) :
 f0 c s = observed c s := by
 unfold f0 observed NMP_prepare.r1_semantic.verify_observed
 apply NMT_CallTree.result_congr
 intro r
 cases r with
 | Err e => rfl
 | Ok p =>
  unfold f1
  apply NMT_CallTree.result_congr
  intro u
  unfold f2
  apply NMT_CallTree.result_congr
  intro r
  cases r with
  | Err e => rfl
  | Ok t =>
   unfold f3
   apply NMT_CallTree.result_congr
   intro pair
   rcases pair with ⟨r,after⟩
   cases r with
   | Err e => rfl
   | Ok ch => rfl
/-- The state-machine fold is about the actual fresh emitted137 definition.
This does not install the child laws or claim the canonical resource RowSpec. -/
theorem emitted {H W : Type} (c : Calls) (s : Parent H W) :
 NMT_CallTree.erase (NMP_ObservedSteps.body c s) = observed c s :=
 (fold0 c s).trans (source c s)
#print axioms source
#print axioms emitted
end AspisR1.NMP_ObservedSuffix
