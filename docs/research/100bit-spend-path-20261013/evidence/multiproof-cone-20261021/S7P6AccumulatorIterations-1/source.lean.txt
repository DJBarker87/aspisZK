import S7JoinAccumulation

/-! Transaction-local composition of the complete accumulator carrier port.
Every step's success and phase safety are derived. Wire query_values and
source geometry/fold/caller adoption remain separate obligations. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S7P6AccumulatorIterations
open Aeneas Aeneas.Std Result
open S7JoinAccumulation S7JoinBackendCarriers
open S7Kani2AccumulatorLoop (K E)
open S7Kani3CallerTrace (Sum PushTrace)
open S7JoinRowsTrace (Progress)

structure Invariant (old : S8OwnedP6Finish.Weights) (t : Nat) (s : State) (sum : Sum) : Prop where
  width : s.output.val.length=64
  power : Canonical s.power
  rhs : CanonicalE s.rhs
  history : PushTrace old s.raw sum
  phase : Progress t 0 s.raw

/-- Exact source-port effects, retained at every reached call rather than
replaced by an arbitrary list of successful states. -/
structure Effect (s out : State) (sum sumOut : Sum) (rho : K)
    (node : U32) (value : E) : Prop where
  execution : accumulate s rho node value=ok out
  frame : out.output=s.output
  next : out.next.val=s.next.val+1
  power : decodeK out.power=decodeK s.power*decodeK rho
  rhs0 : decodeK out.rhs.c0=decodeK s.rhs.c0+decodeK value.c0*decodeK s.power
  rhs1 : decodeK out.rhs.c1=decodeK s.rhs.c1+decodeK value.c1*decodeK s.power
  weights : ∀ i, i<64 → ∀ k : Fin 4,
    (sumOut i k : ZMod AspisCircleGroupOrder.P)=(sum i k : ZMod AspisCircleGroupOrder.P)+
      (S7Kani2OwnedRowRefinement.powerLimb s.power k).val*
        AspisCircleTensorBinding.naturalLineValue (S7JoinBasisMachine.decode node) i

inductive Trace (rho : K) (nodes : Nat → U32) (values : Nat → E) :
    Nat → State → Sum → State → Sum → Prop
  | nil (s sum) : Trace rho nodes values 0 s sum s sum
  | cons {n s sum out sumOut final finalSum}
      (effect : Effect s out sum sumOut rho (nodes s.next.val) (values s.next.val))
      (tail : Trace rho nodes values n out sumOut final finalSum) :
      Trace rho nodes values (n+1) s sum final finalSum

def run (rho : K) (nodes : Nat → U32) (values : Nat → E) : Nat → State → Result State
  | 0,s => ok s
  | n+1,s => do
    let out ← accumulate s rho (nodes s.next.val) (values s.next.val)
    run rho nodes values n out

/-- No successful-call, preservation, basis, row, RHS or power theorem is
supplied by the caller. The whole finite port run follows from the inherited
proved complete single-accumulation certificate. -/
theorem total (old : S8OwnedP6Finish.Weights) (rho : K) (nodes : Nat → U32)
    (values : Nat → E) (n t : Nat) (s : State) (sum : Sum)
    (initial : Invariant old t s sum) (hrho : Canonical rho)
    (hvalues : ∀ j, j<22 → CanonicalE (values j))
    (counter : s.next.val+n≤22) (phase : t+n≤22) :
    ∃ out sumOut, run rho nodes values n s=ok out ∧
      Invariant old (t+n) out sumOut ∧
      out.next.val=s.next.val+n ∧ Trace rho nodes values n s sum out sumOut := by
  induction n generalizing t s sum with
  | zero => exact ⟨s,sum,rfl,by simpa using initial,by omega,.nil s sum⟩
  | succ n ih =>
    obtain ⟨out,sumOut,exec,frame,history,progress,crhs,cpower,next,power,rhs0,rhs1,weights⟩ :=
      S7JoinAccumulation.total_exact old s sum rho (nodes s.next.val) (values s.next.val) t
        initial.width (by omega) (by omega) initial.power hrho initial.rhs
        (hvalues s.next.val (by omega)) initial.history initial.phase
    have inv : Invariant old (t+1) out sumOut :=
      ⟨by rw [frame]; exact initial.width,cpower,crhs,history,progress⟩
    obtain ⟨final,finalSum,tail,finalInv,finalNext,trace⟩ := ih (t+1) out sumOut inv
      (by omega) (by omega)
    refine ⟨final,finalSum,?_,?_,by omega,?_⟩
    · simp only [run,exec,bind_tc_ok,tail]
    · convert finalInv using 1 <;> omega
    · exact .cons ⟨exec,frame,next,power,rhs0,rhs1,weights⟩ trace

#print axioms total
end AspisR1.S7P6AccumulatorIterations
end
