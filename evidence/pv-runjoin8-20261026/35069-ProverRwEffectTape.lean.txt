import R1Z.ProverRwEffectSource

/-! A suspended call at the exact emitted fill boundary. Interpretation at a
fixed dictionary is checked; native/world association remains open. Tape
exhaustion suspends the request rather than inventing a native RNG error. -/
set_option autoImplicit false
namespace R1Z.ProverRwEffectTape
open Aeneas Aeneas.Std Result ControlFlow ProverRwFull
open ProverRwEffectSource
variable [ExternalTypes] [ExternalFuns]

inductive Call where
  | stop : Result Outcome → Call
  | read : Slice U8 → (Reply → Result Outcome) → Call

def emit (nonce : Array U8 32#usize) (limit retry : Usize) : Call :=
  if retry < limit then
    match before with
    | .ok (input,back) => .read input (after nonce retry back)
    | .fail e => .stop (.fail e)
    | .div => .stop .div
  else .stop (.ok (.done (.Err .RepeatedZeroBlock)))

def pure (call : Call) : Result Outcome :=
  match call with
  | .stop out => out
  | .read input resume => do
    let reply ← getrandom.fill input
    resume reply

theorem pure_eq (nonce : Array U8 32#usize) (limit retry : Usize) :
    pure (emit nonce limit retry) =
      aspis_prover.state_only_entropy.StateOnlyAttemptSecrets.generate_for_mask_nonce_loop.body
        nonce limit retry := by
  rw [← staged_eq]
  unfold emit staged
  split
  · cases h : (before : Result (Slice U8 × Back)) with
    | fail e => simp [h, pure]
    | div => simp [h, pure]
    | ok pair => rcases pair with ⟨input,back⟩; simp [h, pure]
  · rfl

structure World where
  tape : List (Result Reply)
  reads : List (Slice U8 × Result Reply)

/-- A stopped source outcome, an unserved request, or a remaining retry.
The fuel boundary is a proof interpreter boundary, never a native error. -/
inductive Boundary where
  | returned : Result Status → Boundary
  | request : Slice U8 → (Reply → Result Outcome) → Boundary
  | retry : Usize → Boundary

structure Execution where
  boundary : Boundary
  world : World

def advance (input : Slice U8) (reply : Result Reply) (rest : List (Result Reply))
    (world : World) : World := ⟨rest,world.reads ++ [(input,reply)]⟩

def resumeResult (resume : Reply → Result Outcome) (reply : Result Reply) : Result Outcome := do
  let value ← reply
  resume value

def finish (out : Result Outcome) : Boundary :=
  match out with
  | .fail e => .returned (.fail e)
  | .div => .returned .div
  | .ok (.done status) => .returned (.ok status)
  | .ok (.cont next) => .retry next

def step (nonce : Array U8 32#usize) (limit retry : Usize) (world : World) : Execution :=
  match emit nonce limit retry with
  | .stop out => ⟨finish out,world⟩
  | .read input resume =>
    match world.tape with
    | [] => ⟨.request input resume,world⟩
    | reply :: rest => ⟨finish (resumeResult resume reply),advance input reply rest world⟩

def run (nonce : Array U8 32#usize) (limit : Usize) : Nat → Usize → World → Execution
  | 0, retry, world => ⟨.retry retry,world⟩
  | fuel+1, retry, world =>
    let out := step nonce limit retry world
    match out.boundary with
    | .retry next => run nonce limit fuel next out.world
    | _ => out

/-- All requested replies remain in their original order, including the reply
whose continuation fails/diverges or returns an entropy error. -/
theorem step_tape (nonce : Array U8 32#usize) (limit retry : Usize) (world : World) :
    (step nonce limit retry world).world.reads.map Prod.snd ++
        (step nonce limit retry world).world.tape = world.reads.map Prod.snd ++ world.tape := by
  unfold step
  cases emit nonce limit retry with
  | stop out => rfl
  | read input resume =>
    cases h : world.tape with
    | nil => simp [h]
    | cons reply rest => simp [advance, List.map_append, List.append_assoc, h]

theorem run_tape (nonce : Array U8 32#usize) (limit : Usize) (fuel : Nat)
    (retry : Usize) (world : World) :
    (run nonce limit fuel retry world).world.reads.map Prod.snd ++
      (run nonce limit fuel retry world).world.tape = world.reads.map Prod.snd ++ world.tape := by
  induction fuel generalizing retry world with
  | zero => rfl
  | succ fuel ih =>
    simp only [run]
    split
    · exact (ih _ _).trans (step_tape nonce limit retry world)
    · exact step_tape nonce limit retry world

/-- Generic finite-tape/source-control refinement: no callback-result or
output-equivalence premise. This uses the factored actual emitted continuation;
it does not identify the world interpreter with native source execution. -/
theorem step_served (nonce : Array U8 32#usize) (limit retry : Usize)
    (input : Slice U8) (resume : Reply → Result Outcome)
    (h : emit nonce limit retry = .read input resume)
    (reply : Result Reply) (rest : List (Result Reply)) (reads : List (Slice U8 × Result Reply)) :
    step nonce limit retry ⟨reply::rest,reads⟩ =
      ⟨finish (resumeResult resume reply),⟨rest,reads ++ [(input,reply)]⟩⟩ := by
  simp only [step,h,advance]

/-- Boundary regression only: both actual fill input buffers are fresh zeros;
the world records zero then nonzero without equating their responses. This
alone makes no assertion that the native owner succeeds. -/
theorem zero_then_nonzero_reads (rest : List (Result Reply)) :
    let zero := ProverRwEntropyObstruction.zeroInput
    let one := ProverRwEntropyObstruction.oneOutput
    let r0 : Result Reply := .ok (.Ok (),zero)
    let r1 : Result Reply := .ok (.Ok (),one)
    let w : World := ⟨r0::r1::rest,[]⟩
    let w1 := advance zero r0 (r1::rest) w
    let w2 := advance zero r1 rest w1
    w2.reads = [(zero,r0),(zero,r1)] ∧ w2.tape = rest := by
  exact ⟨rfl,rfl⟩

#print axioms pure_eq
#print axioms step_tape
#print axioms run_tape
#print axioms step_served
#print axioms zero_then_nonzero_reads
end R1Z.ProverRwEffectTape
