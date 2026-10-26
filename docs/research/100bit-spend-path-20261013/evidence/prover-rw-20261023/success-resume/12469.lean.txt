import R1Z.ProverRwOuterFrames
set_option autoImplicit false
namespace R1Z.ProverRwOrderedOracle
open Aeneas Aeneas.Std Result
abbrev Request := Slice (Slice U8)
abbrev Answer := Array U8 32#usize
structure Entry where
  request : Request
  answer : Result Answer
structure Execution (A : Type) where
  result : Result A
  history : List Entry

def pure {A : Type} (a : A) : Execution A := ⟨.ok a,[]⟩
def native {A : Type} (r : Result A) : Execution A := ⟨r,[]⟩
def query (hash : Request → Result Answer) (q : Request) : Execution Answer :=
  ⟨hash q,[⟨q,hash q⟩]⟩
def bind {A B : Type} (x : Execution A) (f : A → Execution B) : Execution B :=
  match x.result with
  | .ok a => let next := f a; ⟨next.result,x.history++next.history⟩
  | .fail e => ⟨.fail e,x.history⟩
  | .div => ⟨.div,x.history⟩
instance : Monad Execution where
  pure := pure
  bind := bind

theorem result_bind {A B : Type} (x : Execution A) (f : A → Execution B) :
    (bind x f).result=(x.result >>= fun a => (f a).result) := by
  unfold bind
  cases x.result <;> rfl

theorem result_native {A : Type} (r : Result A) : (native r).result=r := rfl
theorem result_query (hash : Request → Result Answer) (q : Request) :
    (query hash q).result=hash q := rfl
theorem result_pure {A : Type} (a : A) : (pure a).result=.ok a := rfl

theorem failed_keeps_history {A B : Type} (x : Execution A) (f : A → Execution B)
    (error : Error) (failed : x.result=.fail error) : (bind x f).history=x.history := by
  simp only [bind,failed]
theorem diverged_keeps_history {A B : Type} (x : Execution A) (f : A → Execution B)
    (failed : x.result=.div) : (bind x f).history=x.history := by
  simp only [bind,failed]
#print axioms result_bind
#print axioms result_native
#print axioms result_query
#print axioms result_pure
#print axioms failed_keeps_history
#print axioms diverged_keeps_history
end R1Z.ProverRwOrderedOracle
