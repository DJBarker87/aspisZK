import AspisR1SimControl21.Funs
import R1Z.ProverCommitSemantic20
/-! Owned opening-control continuation. All policy functions are explicit
parameters; their concrete source instances and the TLS trace join are open. -/
set_option autoImplicit false
namespace R1Z.ProverCommitTail21
open Aeneas Aeneas.Std Result AspisR1SimControl21
abbrev K := aspis_core.field.QM31
abbrev E := aspis_core.field.wide_exact.WideExact
abbrev Values := Array K 25#usize
abbrev Points := Array (Array K 2#usize) 2#usize
abbrev Queries := Array U32 22#usize
abbrev State (H P : Type) := transcript.control21.Transcript H P
abbrev Output := Values × Points × E × E × E × E × Queries × K
abbrev Trace := alloc.vec.Vec (U16 × Usize × E)
abbrev Outcome := Result ((core.result.Result Output verifier.Error) × (Array U8 32#usize) × Trace)

def finish {H P : Type} (hash : aspis_core.digest.Digest32 H)
    (policy : transcript.control21.Policy P) (state : State H P) (payload : Slice U8)
    (sem : Values) (z : Points) (gamma kappa alpha0 alpha1 : E) : Outcome := do
  let (sample,next) ← transcript.control21.Transcript.queries hash policy state 31#u8 payload
  match sample with
  | core.result.Result.Ok q => do
    let (rho,after) ← transcript.control21.Transcript.scalar_k hash policy next 32#u8
      (Array.to_slice (Std.Array.empty U8))
    ok (core.result.Result.Ok (sem,z,gamma,kappa,alpha0,alpha1,q,rho),after.state,after.trace)
  | core.result.Result.Err e => ok (core.result.Result.Err e,next.state,next.trace)

def setup {H P : Type} (hash : aspis_core.digest.Digest32 H)
    (policy : transcript.control21.Policy P) (oracle : H) (state : Array U8 32#usize)
    (r : sim.Records) (variant : transport.Variant) : Result (E × E × E × E × State H P) := do
  let t ← transcript.control21.Transcript.new hash policy oracle state variant
  let (gamma,t1) ← transcript.control21.Transcript.scalar hash policy t 27#u8 (alloc.vec.Vec.deref r.y1) true
  let (kappa,t2) ← transcript.control21.Transcript.scalar hash policy t1 28#u8 (Array.to_slice r.inactive) false
  let (alpha0,t3) ← transcript.control21.Transcript.scalar hash policy t2 29#u8 (alloc.vec.Vec.deref r.c0) false
  let payload ← alloc.slice.Slice.to_vec core.clone.CloneU8 (Array.to_slice r.folded_root)
  let payload1 ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 payload (alloc.vec.Vec.deref r.c1)
  let (alpha1,t4) ← transcript.control21.Transcript.scalar hash policy t3 30#u8 (alloc.vec.Vec.deref payload1) false
  ok (gamma,kappa,alpha0,alpha1,t4)

/-- Exact extracted suffix split into rows 27–30 and the query/rho
continuation, retaining failures and the native-trace reference state. -/
theorem tail_schedule {H P : Type} (hash : aspis_core.digest.Digest32 H)
    (policy : transcript.control21.Policy P) (oracle : H) (state : Array U8 32#usize)
    (sem : Values) (z : Points) (r : sim.Records) (variant : transport.Variant) :
    sim.tail_control21 hash policy oracle state sem z r variant =
      (do let (gamma,kappa,alpha0,alpha1,t4) ← setup hash policy oracle state r variant
          finish hash policy t4 (alloc.vec.Vec.deref r.fin) sem z gamma kappa alpha0 alpha1) := by
  simp only [sim.tail_control21,setup,finish,lift,bind_tc_ok,bind_assoc,pure_bind]
  rfl

/-- Query rejection retains advanced state and all earlier trace entries;
row 32 is not evaluated after this branch. -/
theorem query_failure {H P : Type} (hash : aspis_core.digest.Digest32 H)
    (policy : transcript.control21.Policy P) (state next : State H P) (payload : Slice U8)
    (sem : Values) (z : Points) (gamma kappa alpha0 alpha1 : E) (error : verifier.Error)
    (rejected : transcript.control21.Transcript.queries hash policy state 31#u8 payload =
      ok (core.result.Result.Err error,next)) :
    finish hash policy state payload sem z gamma kappa alpha0 alpha1 =
      ok (core.result.Result.Err error,next.state,next.trace) := by
  simp only [finish,rejected,bind_tc_ok,Aeneas.Std.uncurry_apply_pair]

/-- A successful query sample is followed by rho on row 32 with empty
payload. Its final state and trace, rather than just the returned values,
are part of the continuation result. -/
theorem query_success {H P : Type} (hash : aspis_core.digest.Digest32 H)
    (policy : transcript.control21.Policy P) (state next after : State H P) (payload : Slice U8)
    (sem : Values) (z : Points) (gamma kappa alpha0 alpha1 : E) (q : Queries) (rho : K)
    (sampled : transcript.control21.Transcript.queries hash policy state 31#u8 payload =
      ok (core.result.Result.Ok q,next))
    (last : transcript.control21.Transcript.scalar_k hash policy next 32#u8
      (Array.to_slice (Std.Array.empty U8)) = ok (rho,after)) :
    finish hash policy state payload sem z gamma kappa alpha0 alpha1 =
      ok (core.result.Result.Ok (sem,z,gamma,kappa,alpha0,alpha1,q,rho),after.state,after.trace) := by
  simp only [finish,sampled,bind_tc_ok,Aeneas.Std.uncurry_apply_pair,last]

/-- The accepted 25-row source cone composes with every continuation that
consumes its full returned state, errors and values. No success-only join or
concrete simulator continuation is assumed by this equation. -/
theorem semantic_continuation {H C : Type}
    (hash : AspisR1SimSemantic20.aspis_core.digest.Digest32 H)
    (records : ProverCommitSemantic20.Records) (row : Usize) (remaining : Nat)
    (state : ProverCommitSemantic20.State H) (sem : ProverCommitSemantic20.Values)
    (count : row.val+remaining=25)
    (continuation : (core.result.Result ProverCommitSemantic20.Values
      AspisR1SimSemantic20.r1_wire.Error) × ProverCommitSemantic20.State H → Result C) :
    (AspisR1SimSemantic20.r1_wire.semantic20.rows hash state records row sem >>= continuation) =
      (ProverCommitSemantic20.finite hash records row remaining state sem >>= continuation) := by
  rw [ProverCommitSemantic20.extracted_finite hash records row remaining state sem count]

#print axioms tail_schedule
#print axioms query_failure
#print axioms query_success
#print axioms semantic_continuation
#print axioms AspisR1SimControl21.sim.tail_control21
#print axioms AspisR1SimControl21.transcript.control21.Transcript.queries
end R1Z.ProverCommitTail21
