import NHZ_NativeAssociation
import NFS_CallerDomains
import NFS_QueryLoopRoot
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIA_EventInterpretation
open Aeneas Aeneas.Std Result CheckpointBytes5Effect AspisR1Stage2
open Port3_NativeQueryBody NFP_TraceTypes

/-- Structural absence of read nodes, rather than a claim inferred from the
return type. This predicate is about effect syntax, not arbitrary native code. -/
inductive NoReads : {A : Type} → Code A → Prop where
 | done {A : Type} (a : A) : NoReads (.done a)
 | step {A B : Type} (r : Result B) (k : B → Code A)
     (next : ∀ b, NoReads (k b)) : NoReads (.step r k)

def pureCall {A : Type} (r : Result A) : Code Unit := .step r (fun _ => .done ())

/-- The exact callee invocations named by each NFP event, on the closed query
installation. No digest-bearing constructor is introduced into this alphabet.
The native interpretation of the pureCall boundary is audited separately. -/
def eventCode (base : Ops) (e : Event) : Code Unit :=
 let ops := NFS_CallerDomains.ops base
 match e with
 | .opening proof i => pureCall (ops.op11 proof i)
 | .dots q g => pureCall (ops.op20 q g)
 | .trace tag i value => pureCall (ops.op15 tag i value)
 | .geometry geometry i => pureCall (ops.op18 geometry i)
 | .circle alpha values inverse => pureCall (ops.op17 alpha values inverse)
 | .fields q => pureCall (ops.op0 4#usize
     (verifier.candidate.query_values.closure.Insts.CoreOpsFunctionFnMutTupleUsizeWideExact ops) q)
 | .line alpha values inverse => pureCall (ops.op16 alpha values inverse)
 | .product a b => pureCall (ops.op7 a b)
 | .double a => pureCall (ops.op8 a)
 | .one => pureCall ops.op5
 | .subtract a b => pureCall (ops.op6 a b)
 | .accumulate p a node value pending =>
     pureCall (verifier.accumulate_batched_with_node ops p a node value pending)

/-- Use NFS's complete selection, so no arbitrary callback survives this
model interpretation. Native effect provenance is still a separate claim. -/
theorem event_seed_independent (first second : Ops) (event : Event) :
 eventCode first event=eventCode second event := by
 unfold eventCode
 rw [NFS_CallerDomains.no_seed first second]

theorem event_no_reads (base : Ops) (event : Event) : NoReads (eventCode base event) := by
 cases event <;> exact .step _ _ (fun _ => .done ())

/-- Every terminal, including failure/divergence, preserves the prior context
and earlier query occurrences. Nothing is inferred about an uninstalled native
callback from this theorem. -/
theorem no_reads_trace {A : Type} {code : Code A} (pureCode : NoReads code)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) :
 ∃ out, NGQ_Cuts.Trace hashv code out [] := by
 induction pureCode with
 | done a => exact ⟨.ok a,.done a⟩
 | step r k next ih =>
   cases r with
   | ok b => obtain ⟨out,tail⟩ := ih b; exact ⟨out,.stepOk _ _ b rfl _ _ tail⟩
   | fail e => exact ⟨.fail e,.stepFail _ _ e rfl⟩
   | div => exact ⟨.div,.stepDiv _ _ rfl⟩

theorem no_reads_frame {A C : Type} {code : Code A} (pureCode : NoReads code)
 (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (context : C) (before : SdkC_Source.Log) :
 ∃ out, (context,SdkC_Source.run hashv code before)=(context,(out,before)) := by
 obtain ⟨out,trace⟩ := no_reads_trace pureCode hashv
 exact ⟨out,by rw [NGQ_Cuts.run trace before,List.append_nil]⟩

def eventsCode (base : Ops) : List Event → Code Unit
 | [] => .done ()
 | e::es => CheckpointBytes5Effect.bind (eventCode base e) (fun _ => eventsCode base es)

theorem bind_no_reads {A B : Type} {code : Code A} (head : NoReads code)
 (k : A → Code B) (tail : ∀ a, NoReads (k a)) :
 NoReads (CheckpointBytes5Effect.bind code k) := by
 induction head with
 | done a => exact tail a
 | step r next h ih => exact .step r _ ih

theorem events_no_reads (base : Ops) (events : List Event) : NoReads (eventsCode base events) := by
 induction events with
 | nil => exact .done ()
 | cons e es ih => exact bind_no_reads (event_no_reads base e) _ (fun _ => ih)

/-- All twelve cases, duplicates and stopped prefixes retain an empty digest
log. This is the event interpreter's packet; native cut association is separate. -/
theorem events_packet (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest)
 (base : Ops) (events : List Event) :
 ∃ out, NHZ_DRIVER.Cuts hashv (eventsCode base events) out [] := by
 obtain ⟨out,t⟩ := no_reads_trace (events_no_reads base events) hashv
 exact ⟨out,.leaf t⟩

#print axioms event_seed_independent
#print axioms event_no_reads
#print axioms no_reads_trace
#print axioms no_reads_frame
#print axioms bind_no_reads
#print axioms events_no_reads
#print axioms events_packet
end AspisR1.NIA_EventInterpretation
