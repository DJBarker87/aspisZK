import PV_RJ4IDB_NativeFactor
import PV_RJ4IDB_SourceTrace
import R1Z.ProverCommitFuelJoin22
/-! EXPERIMENTAL, NOT ADOPTED (D478). Event-retaining interface; the deployed
Runtime and headline remain unchanged. The timing reconstruction proof is
reused from PV_L1C_TimingKey, whose cached object was deleted by that line.
All acquisition, causal-prefix and joint noise laws remain ordinary P links. -/
set_option autoImplicit false
noncomputable section
namespace PV_EVHD_Interface
open PV_RJ4IDB R0Z R0Z.FsStatement R1Z
def timingSlot : NativeEvent → NativeEvent
 | .wall _ => .wall []
 | e => e

def restoreTimes : List NativeEvent → List Bytes → Option (List NativeEvent × List Bytes)
 | [],ts => some ([],ts)
 | .wall _ :: _,[] => none
 | .wall _ :: es,t::ts => (restoreTimes es ts).map (fun p => (.wall t::p.1,p.2))
 | e::es,ts => (restoreTimes es ts).map (fun p => (e::p.1,p.2))

theorem restore_times (es : List NativeEvent) (tail : List Bytes) :
 restoreTimes (es.map timingSlot) (nativeTimes es ++ tail) = some (es,tail) := by
 induction es with
 | nil => rfl
 | cons e es ih =>
   simp only [nativeTimes] at ih
   cases e <;> simp only [List.map_cons,timingSlot,nativeTimes,List.filterMap_cons,
     List.cons_append,List.nil_append,restoreTimes,ih,Option.map_some]

def timingKey {A : Type} (t : NativeTrace A) :
 (List NativeEvent × Terminal A) × List Bytes :=
 ((t.events.map timingSlot,t.terminal),nativeTimes t.events)

/-- Counts, oracle, allocation/address/physical/durable/environment events and
cross-channel order stay in the context. No success conditioning occurs. -/
theorem timing_key_injective {A : Type} : Function.Injective (@timingKey A) := by
 intro l r h
 have hs := congrArg (fun p => p.1.1) h
 have ht := congrArg (fun p => p.1.2) h
 have hw := congrArg Prod.snd h
 have hl := restore_times l.events []
 have hr := restore_times r.events []
 have he : l.events = r.events := by
   have hx : some (l.events,([] : List Bytes)) = some (r.events,[]) := by
     rw [← hl,← hr]
     change restoreTimes (l.events.map timingSlot) (nativeTimes l.events ++ []) =
       restoreTimes (r.events.map timingSlot) (nativeTimes r.events ++ [])
     rw [show l.events.map timingSlot = r.events.map timingSlot from hs,
       show nativeTimes l.events = nativeTimes r.events from hw]
   exact congrArg Prod.fst (Option.some.inj hx)
 cases l; cases r; cases he; cases ht; rfl


/-- EXPERIMENTAL: option-B signal accompanies the ENTIRE ordered observation.
Every finite divergence prefix is a separate invocation of this interface. -/
def observe {A Signal : Type} (signal : Signal) (trace : NativeTrace A) :
    Signal × Observation A := (signal, nativeObservation trace)

/-- EXPERIMENTAL: a public completion kernel. Env supplies joint environmental
and timing noise; it is not witness input. Public is fixed by the invocation.
complete must generate timings AND their copies in JSON/stdout consistently. -/
structure Completion (Public Signal Env Core A : Type) where
  signal : Public → Env → Signal
  complete : Public → Signal → Env → Core → NativeTrace A

/-- EXPERIMENTAL: the same signal on the original good common samples. Its
witness independence requires the public environment marginal link as well. -/
def Link_Signal {S Signal : Type} (bad : S → Prop) (real sim : S → Signal) : Prop :=
  ∀ s, ¬bad s → real s = sim s

/-- EXPERIMENTAL: all ordered non-wall context, timing slots and terminals,
including partial writes, errors, aborts and divergence prefixes. -/
def Link_Context {S A : Type} (bad : S → Prop)
    (real sim : S → NativeTrace A) : Prop :=
  ∀ s, ¬bad s → (timingKey (real s)).1 = (timingKey (sim s)).1

/-- EXPERIMENTAL D166: exact JOINT timing on the SAME D163 coupling; not
marginal timing, constant time, or elapsed time declared public. -/
def Link_Timing {S A : Type} (bad : S → Prop)
    (real sim : S → NativeTrace A) : Prop :=
  ∀ s, ¬bad s → nativeTimes (real s).events = nativeTimes (sim s).events

theorem full_agreement {S A Signal : Type} (bad : S → Prop)
    (real sim : S → NativeTrace A) (rs ss : S → Signal)
    (context : Link_Context bad real sim) (timing : Link_Timing bad real sim)
    (signal : Link_Signal bad rs ss) :
    ∀ s, ¬bad s → observe (rs s) (real s) = observe (ss s) (sim s) := by
  intro s hs
  have ht : real s = sim s := timing_key_injective
    (Prod.ext (context s hs) (timing s hs))
  rw [ht, signal s hs]

/-- EXPERIMENTAL D163 adapter. No field is added to the three-field trust list;
the coupling retains both marginals and exactly the original bad event. -/
def eventJoin {R M A Signal : Type} [Fintype R] [Fintype M]
    (real : R → NativeTrace A) (sim : M → NativeTrace A)
    (rs : R → Signal) (ss : M → Signal)
    (old : Fin 8 → M → Prop) (queries : M → List ProverCommitSeedEvent19.Entry)
    (cp : R0Z.FsGood.Coupling R ((M × OracleAnswer) × ProverCommitFuelJoin22.Tape))
    (context : Link_Context (fun s => ∃ i, ProverCommitFuelJoin22.bad old queries i (cp.toM s))
      (fun s => real (cp.toR s)) (fun s => sim (cp.toM s).1.1))
    (timing : Link_Timing (fun s => ∃ i, ProverCommitFuelJoin22.bad old queries i (cp.toM s))
      (fun s => real (cp.toR s)) (fun s => sim (cp.toM s).1.1))
    (signal : Link_Signal (fun s => ∃ i, ProverCommitFuelJoin22.bad old queries i (cp.toM s))
      (fun s => rs (cp.toR s)) (fun s => ss (cp.toM s).1.1)) :
    ProverCommitFuelJoin22.RunJoin (fun r => observe (rs r) (real r))
      (fun m => observe (ss m) (sim m)) old queries where
  cp := cp
  agreement := full_agreement _ _ _ _ _ context timing signal

#print axioms restore_times
#print axioms timing_key_injective
#print axioms full_agreement
#print axioms eventJoin
end PV_EVHD_Interface
