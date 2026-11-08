import NNG_TryObservation345
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TryAssociation345
open Aeneas Aeneas.Std Result NMT_345 NMT_CallTree NNG_Observed136

theorem source {A B : Type} (f : A → B) (r : Result (core.result.Result A PE))
 (next : A → Code Ret) (tail : B → RSL.Obs (Except RSL.ProgramError RSL.Bytes))
 (events : Event → List RSL.Event)
 (later : ∀ a, r=ok (.Ok a) → observation NNG_ChildSource345.port events (next a)=tail (f a)) :
 observation NNG_ChildSource345.port events (NNG_TreeBase345.tryCode r next)=
 NNG_Obs345.tryObs (NNG_Observe345.observe f r) tail := by
 cases r with
 | fail e=>rfl
 | div=>rfl
 | ok reply=>
  cases reply with
  | Err e=>rfl
  | Ok a=>exact later a rfl
#print axioms source
end AspisR1.NNG_TryAssociation345
