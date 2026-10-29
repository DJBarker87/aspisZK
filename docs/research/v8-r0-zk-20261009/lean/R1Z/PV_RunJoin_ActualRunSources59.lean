import R1Z.PV_RunJoin_NativeCallback55
/-! Symbolic source calls for the fixed callback families. These definitions
retain failures and divergence and do not evaluate a fixture or a prover run. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualRunSources59
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
variable [ExternalTypes] [ExternalFuns]

def prepare (p : Phase) := prover.prepare_opening .S2 p.hash p.backend p.sem

def salts (p : Phase) := prover.derive_private_salts p.salts.1 p.salts.2 p.hash 114#u8

def finish (p : Phase) : Result (core.result.Result prover.Publication verifier.Error) := do
  let prepared ← prepare p
  match prepared with
  | .Err e => ok (.Err e)
  | .Ok prepared =>
    let privateSalts ← salts p
    match privateSalts with
    | .Err e => ok (.Err e)
    | .Ok privateSalts => prover.finish_opening .S2 p.hash prepared privateSalts

/-- Reconstruct exactly tag 30's payload from the returned root and round
bytes; the scalar call is symbolic, with its original transcript and hash. -/
def alpha1 (p : Phase) : Result (Option aspis_core.field.wide_exact.WideExact) := do
  let prepared ← prepare p
  match prepared with
  | .Err _ => ok none
  | .Ok prepared =>
    let publication ← finish p
    match publication with
    | .Err _ => ok none
    | .Ok publication =>
      let root ← Aeneas.Std.lift (Array.to_slice publication.root)
      let payload ← alloc.slice.Slice.to_vec core.clone.CloneU8 root
      let payload ← alloc.vec.Vec.extend_from_slice core.clone.CloneU8 payload
        (alloc.vec.Vec.deref publication.c1bytes)
      let (a,_) ← host_transcript.Transcript.scalar
        aspis_core.digest.LegacyHashFn.Insts.Aspis_coreDigestDigest32
        prepared.transcript 30#u8 (alloc.vec.Vec.deref payload) false
      ok (some a)

theorem prepare_return (p : Phase) (prepared : prover.PreparedOpening)
    (success : prover.prepare_opening .S2 p.hash p.backend p.sem=ok (.Ok prepared)) :
    prepare p=ok (.Ok prepared) := success

theorem finish_return (p : Phase) (prepared : prover.PreparedOpening)
    (privateSalts : host_commitment.PrivateSalts) (publication : prover.Publication)
    (hp : prepare p=ok (.Ok prepared)) (hs : salts p=ok (.Ok privateSalts))
    (hf : prover.finish_opening .S2 p.hash prepared privateSalts=ok (.Ok publication)) :
    finish p=ok (.Ok publication) := by
  simp only [finish,hp,hs,bind_tc_ok,hf]

#print axioms prepare
#print axioms salts
#print axioms finish
#print axioms alpha1
#print axioms prepare_return
#print axioms finish_return
end R1Z.PV_RunJoin_ActualRunSources59
