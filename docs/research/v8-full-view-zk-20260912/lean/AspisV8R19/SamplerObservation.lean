import AspisV8R19.SqueezeOracleBridge

/-! Successful-call observation for the generated sampler. A backend failure
or divergence is still a Result failure/divergence, not a successful trace.
Sampler exhaustion errors are ordinary successful Result values and retain
their trace. Complete correspondence is proved separately, not by erasure. -/
set_option autoImplicit false
namespace AspisV8R19.SamplerObservation
open Aeneas Aeneas.Std Result ControlFlow

abbrev Input := Slice (Slice U8)
abbrev Block := Array U8 32#usize
abbrev Trace := List (Input × Block)
abbrev Observed (α : Type) := StateT Trace Result α

def observeHash (hash : Input → Result Block) (input : Input) : Observed Block :=
  fun history => do
    let out ← hash input
    .ok (out,history ++ [(input,out)])

def observedLoop {S A : Type} (body : S → Observed (ControlFlow S A))
    (initial : S) : Observed A := fun history =>
  loop (fun (s,t) => do
    let (r,t1) ← body s t
    match r with
    | .cont s1 => .ok (.cont (s1,t1))
    | .done a => .ok (.done (a,t1))) (initial,history)

def decodeTrace (history : Trace) : List (DuplexFrames.Bytes × SourceDuplexStep.State) :=
  history.map (fun (input,out) => (SqueezeOracleBridge.flatten input,SqueezeOracleBridge.decodeState out))

theorem observe_success (hash : Input → Result Block) (input : Input) (out : Block)
    (h : hash input=.ok out) (history : Trace) :
    observeHash hash input history=.ok (out,history++[(input,out)]) := by
  simp only [observeHash,h,bind_tc_ok]

theorem observe_failure (hash : Input → Result Block) (input : Input) (e : Error)
    (h : hash input=.fail e) (history : Trace) :
    observeHash hash input history=.fail e := by
  simp only [observeHash,h,bind_tc_fail]

theorem decode_append (a b : Trace) : decodeTrace (a++b)=decodeTrace a++decodeTrace b := by
  exact List.map_append

#print axioms observe_success
#print axioms observe_failure
#print axioms decode_append
end AspisV8R19.SamplerObservation
