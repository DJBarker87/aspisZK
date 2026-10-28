import Mathlib.Data.List.Basic
namespace R1Z.PV_RDB2C_PublicRequests
structure Request where
  size : Nat
  alignment : Nat
  reallocFrom : Option Nat
  deriving DecidableEq

/-- Public traces record request order, sizes and alignments. The allocator's
private result and address are separate. Failure stops the remaining suffix. -/
def execute {S : Type} (step : Request → S → Bool × S) : List Request → S → List Request × S
  | [],s => ([],s)
  | r::rs,s =>
    let (success,s') := step r s
    if success then
      let (seen,s'') := execute step rs s'
      (r::seen,s'')
    else ([r],s')

theorem public_schedule {P H : Type} (schedule : P → List Request)
    (public : P) (left right : H) :
    (fun (p : P) (_ : H) => schedule p) public left =
    (fun (p : P) (_ : H) => schedule p) public right := rfl

theorem same_runtime {P H S : Type} (schedule : P → List Request)
    (step : Request → S → Bool × S) (public : P) (left right : H) (state : S) :
    execute step ((fun p (_ : H) => schedule p) public left) state =
    execute step ((fun p (_ : H) => schedule p) public right) state := rfl

theorem failure_before_suffix {S : Type} (step : Request → S → Bool × S)
    (r : Request) (rs : List Request) (s after : S) (h : step r s=(false,after)) :
    execute step (r::rs) s=([r],after) := by simp [execute,h]

/-- This is a conditional factorisation theorem, not a proof that any row's
schedule factors through its public input. Every instance needs a source gate. -/
theorem factor_transport {P H S : Type} (source : P → H → List Request)
    (schedule : P → List Request) (factor : ∀ p h, source p h=schedule p)
    (step : Request → S → Bool × S) (p : P) (a b : H) (s : S) :
    execute step (source p a) s=execute step (source p b) s := by rw [factor,factor]

#print axioms public_schedule
#print axioms same_runtime
#print axioms failure_before_suffix
#print axioms factor_transport
end R1Z.PV_RDB2C_PublicRequests
