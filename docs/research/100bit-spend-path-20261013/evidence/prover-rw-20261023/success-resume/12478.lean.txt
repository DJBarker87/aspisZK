import R1Z.ProverRwOrderedOracle
set_option autoImplicit false
namespace R1Z.ProverRwOrderedMonad
open Aeneas Aeneas.Std Result
open ProverRwOrderedOracle

theorem result_bind {A B : Type} (x : Execution A) (f : A → Execution B) :
    (x >>= f).result=(x.result >>= fun a => (f a).result) :=
  ProverRwOrderedOracle.result_bind x f

theorem history_bind {A B : Type} (x : Execution A) (f : A → Execution B) :
    (x >>= f).history=
      match x.result with
      | .ok a => x.history++(f a).history
      | _ => x.history := by
  change (ProverRwOrderedOracle.bind x f).history=_
  unfold ProverRwOrderedOracle.bind
  cases x.result <;> rfl
#print ProverRwOrderedOracle.instMonadExecution
#print axioms result_bind
#print axioms history_bind
end R1Z.ProverRwOrderedMonad
