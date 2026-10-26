import R1Z.PV_L1_Lockstep

/-! Explicit uninstalled callback obligations, one field per privacy-ledger
row. This structure ORGANIZES premises; it discharges none of them.
Phase is the current callback boundary, not a new protocol event or schedule.
Raw inputs are retained in Boundary and related on the SAME paired states.
They are not publicly disclosed or required equal; the L2 source theorem
traceLaw supplies equal source traces for related complete raw inputs. -/
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_L1_Premises
open Aeneas Aeneas.Std Result ControlFlow ProverRwRngCaller
open ProverRwRngCallerControl ProverRwRngCallerReplay PV_L1_Lockstep
variable [NativeTypes] [ErasureFns]

inductive Phase where
  | regular | equalCircle | queryAbort | publication
  deriving DecidableEq, Repr

variable {N L B Core Raw Trace Final : Type}

/-- The adapter's local boundary data. NativePayload must come from a native
producer; naming an arbitrary function here does not install that producer. -/
structure Boundary (N L B Core Raw Trace Final : Type) where
  phase : State N L B → Phase
  core : State N L B → Core
  raw : State N L B → Raw
  rawRelated : Raw → Raw → Prop
  traceRaw : Raw → Trace
  referencePayload : State N L B → List SideChannelL1AttemptRecord.Event
  nativePayload : State N L B → List SideChannelL1AttemptRecord.Event
  observe : Output N L B → Final
  reachable : State N L B → Prop

def regularImage (d : Boundary N L B Core Raw Trace Final) (s : State N L B) :=
  (d.phase s,d.core s,if d.phase s = .regular then some (d.referencePayload s) else none)

def jointAtom (d : Boundary N L B Core Raw Trace Final) (s : State N L B) :=
  (d.phase s,d.core s,d.nativePayload s,d.traceRaw (d.raw s))

/-- Each field is a Prop-valued obligation, never a definitional replacement
of native behavior. V348 is LOCAL: one extracted step and its emitted regular
payload; exceptional callback equations are independently named below. -/
structure PV_L1_Premises (lp rp : Policy N) (lb rb : Body B L)
    (rel : State N L B → State N L B → Prop)
    (d : Boundary N L B Core Raw Trace Final) : Prop where
  v347_native_event_producer : ∀ s, d.reachable s → d.nativePayload s = d.referencePayload s
  v348_joint_mask_count_tls_oracle :
    (∀ a b, rel a b → d.reachable a ∧ d.reachable b) ∧
    LocalLaw lp rp lb rb rel (regularImage d) d.observe
  v349_equal_circle_integration : ∀ a b, rel a b → d.phase a = .equalCircle →
    d.referencePayload a = d.referencePayload b
  v350_query_abort_integration : ∀ a b, rel a b → d.phase a = .queryAbort →
    d.referencePayload a = d.referencePayload b
  v351_part47_composition : ∀ a b, rel a b → d.phase a = .publication →
    d.referencePayload a = d.referencePayload b
  v366_joint_raw_input_coupling : ∀ a b, rel a b → d.rawRelated (d.raw a) (d.raw b)

theorem local_joint_law
    {lp rp : Policy N} {lb rb : Body B L}
    {rel : State N L B → State N L B → Prop}
    {d : Boundary N L B Core Raw Trace Final}
    (p : PV_L1_Premises lp rp lb rb rel d)
    (traceLaw : ∀ a b, d.rawRelated a b → d.traceRaw a = d.traceRaw b) :
    LocalLaw lp rp lb rb rel (jointAtom d) d.observe := by
  constructor
  · intro a b related
    have regular := p.v348_joint_mask_count_tls_oracle.2.atom_eq a b related
    have phases : d.phase a = d.phase b := congrArg Prod.fst regular
    have cores : d.core a = d.core b := congrArg (fun x => x.2.1) regular
    have payload : d.referencePayload a = d.referencePayload b := by
      cases ph : d.phase a with
      | regular =>
        have someEq := congrArg (fun x => x.2.2) regular
        simp only [regularImage,ph,phases.symm,ite_true] at someEq
        exact Option.some.inj someEq
      | equalCircle => exact p.v349_equal_circle_integration a b related ph
      | queryAbort => exact p.v350_query_abort_integration a b related ph
      | publication => exact p.v351_part47_composition a b related ph
    have reachable := p.v348_joint_mask_count_tls_oracle.1 a b related
    have native : d.nativePayload a = d.nativePayload b :=
      (p.v347_native_event_producer a reachable.1).trans
        (payload.trans (p.v347_native_event_producer b reachable.2).symm)
    have traces := traceLaw _ _ (p.v366_joint_raw_input_coupling a b related)
    simp only [jointAtom,phases,cores,native,traces]
  · exact p.v348_joint_mask_count_tls_oracle.2.step_rel

#print axioms local_joint_law
end R1Z.PV_L1_Premises
