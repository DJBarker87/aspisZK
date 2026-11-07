import LIBC_CheckpointDomain
import LIB_Env
set_option autoImplicit false
noncomputable section
namespace LIBC_Checkpoint
open Aeneas Aeneas.Std Result AspisR1 RSL
open CheckpointBytes5Effect
abbrev Args := LIBC_CheckpointDomain.Args
abbrev prepared := LIBC_CheckpointDomain.prepared
abbrev accumulator := LIBC_CheckpointDomain.accumulator
abbrev Domain := LIBC_CheckpointDomain.Domain
def digest (env : Env) : AspisR1Stage2.aspis_core.digest.Digest32 Unit :=
 ⟨⟨⟨fun _ => ok ()⟩⟩,fun _ parts => LIB_Env.hashv env parts⟩
def reply (env : Env) (parts : Parts) : Digest := LIB_Env.nativeKey (env.sha256 (NNC_ResumeEvents.parts parts))
def proofParts (a : Args) := AspisR1Stage2.WireTx2.singletonParts (LIBC_Bytes.raw a.2.2.1)
def publicParts (a : Args) := AspisR1Stage2.WireTx2.singletonParts (LIBC_Bytes.raw a.2.2.2)
def body (a : Args) (env : Env) := CheckpointBytes5Writer.bodySlice (prepared a) (accumulator a)
 (reply env (proofParts a)) (reply env (publicParts a))
def checksumParts (a : Args) (env : Env) := AspisR1Stage2.WireTx2.checksumParts (body a env)
def output (a : Args) (env : Env) := CheckpointBytes5Writer.finish (prepared a) (accumulator a)
 (reply env (proofParts a)) (reply env (publicParts a)) (reply env (checksumParts a env))
def value (a : Args) (env : Env) : Bytes := LIB_Carriers.bytes (output a env)
def calls (a : Args) (env : Env) : Log :=
 [(proofParts a,reply env (proofParts a)),(publicParts a,reply env (publicParts a)),
  (checksumParts a env,reply env (checksumParts a env))]
def events (a : Args) (env : Env) : List Event :=
 (calls a env).map (fun r => .digest (NNC_ResumeEvents.parts r.1) (LIB_Carriers.b32 r.2))
/-- Deterministic writer graph and its one entry Vec allocation. The checked
116-append schedule below proves there is no later growth allocation. -/
def law (a : Args) : Spec Bytes := fun env o => Domain a ∧
 (o=⟨.ret (value a env),events a env⟩ ∨ o=⟨.abort,[]⟩)
def child : Child Args Bytes := ⟨Domain,law⟩
theorem returns (a : Args) (env : Env) : NND_Returned.Returns (child.law a) env (value a env) := by
 intro o r h hr
 rcases h.2 with h | h <;> subst o
 · exact (Exit.ret.inj hr).symm
 · cases hr
theorem call (env : Env) (parts : Parts) : (digest env).digest () parts=ok (reply env parts) := rfl
attribute [local irreducible] CheckpointBytesDecodeC5.sourceBody CheckpointBytes5Writer.bodySlice CheckpointBytes5Writer.finish
/-- Exact parts (including checksum's two partitions), replies, output and
chronological order at the SAME original proof/public input slices. -/
theorem run_model (a : Args) (env : Env) :
 CheckpointBytes5Effect.run (digest env) ()
  (CheckpointBytes5Writer.writer (prepared a) (accumulator a)
   (LIBC_Bytes.raw a.2.2.1) (LIBC_Bytes.raw a.2.2.2)) [] = ok (output a env,calls a env) := by
 simp only [CheckpointBytes5Writer.writer,run_bind,run_read,run_pure,call,bind_tc_ok,Aeneas.Std.uncurry,List.nil_append]
 rfl
/-- F6 direct child association, replacing all upstream successful-result
premises by the equivalent current-pair input clause. -/
theorem source_program (a : Args) (h : Domain a) :
 NGC_KNE_Writer.sourceProgram (prepared a) (accumulator a)
  (LIBC_CheckpointDomain.writer_domain a h) (LIBC_Bytes.raw a.2.2.1) (LIBC_Bytes.raw a.2.2.2) =
 CheckpointBytes5Writer.writer (prepared a) (accumulator a)
  (LIBC_Bytes.raw a.2.2.1) (LIBC_Bytes.raw a.2.2.2) :=
 NGC_KNE_Writer.cohort_program_eq _ _ _ _ _
theorem no_growth (a : Args) (h : Domain a) (hp hu hc : Digest) :
 (NGC_KNE_Schedule.derivedSchedule (prepared a) (accumulator a)
  (LIBC_CheckpointDomain.writer_domain a h) hp hu hc).length=116 ∧
 ∀ step∈NGC_KNE_Schedule.derivedSchedule (prepared a) (accumulator a)
  (LIBC_CheckpointDomain.writer_domain a h) hp hu hc,step.len+step.size≤step.cap :=
 NGC_KNE_Final.schedule_facts _ _ _ hp hu hc
theorem graph (a : Args) (env : Env) (o : Obs Bytes) :
 child.law a env o ↔ Domain a ∧ (o=⟨.ret (value a env),events a env⟩ ∨ o=⟨.abort,[]⟩) := Iff.rfl
#print axioms returns
#print axioms call
#print axioms run_model
#print axioms source_program
#print axioms no_growth
#print axioms graph
end LIBC_Checkpoint
