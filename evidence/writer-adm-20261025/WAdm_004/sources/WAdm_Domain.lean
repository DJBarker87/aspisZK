import WAdm_Arithmetic
import Tx1Q_Control
import Port5Q2_Prepared
set_option autoImplicit false
noncomputable section
open Aeneas Aeneas.Std Result
namespace AspisR1.WAdm_Domain
open Tx1Q_Carriers

/-- Immutable preparation owner on its own successful return, not a writer
output, query output, or native/reference agreement. -/
structure SessionAPrepare (installed : AspisR1CurrentCaller.Ops) : Prop where
  accepted : ∀ {H : Type} (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (proof : Slice U8) (zero : C.E) (p : C.P) (scratch : Array C.E 29#usize),
    AspisR1CurrentCaller.verifier.candidate.prepare installed D semantic proof hash none
      (Array.repeat 29#usize zero) = ok (.Ok p,scratch) →
    Port5Q2_Prepared.PreparedFields (prepared p)

/-- Exact value-domain of production_buffers_writer; no output equality or
native execution is contained in this structure. Raw K and query words are
unrestricted by that certificate. -/
structure Admitted (p : AspisR1Stage2.verifier.Prepared)
    (a : AspisR1Stage2.verifier.Accumulator) (proof pub : Slice U8) : Prop where
  variant : p.variant = .S2
  size : a.weights.val.length = 64
  next : a.next.val = 10
  gamma : Port4C_QueryArithmetic.CanonE p.gamma
  kappa : Port4C_QueryArithmetic.CanonE p.kappa
  alpha : ∀ x ∈ p.alpha.val, Port4C_QueryArithmetic.CanonE x
  claim : Port4C_QueryArithmetic.CanonE p.claim
  rhs : Port4C_QueryArithmetic.CanonE a.rhs
  proofLength : proof.val.length = 57607
  publicLength : pub.val.length = 1880

/-- The SAME run supplies every bounded writer value guard. Runtime/physical
carrier interpretation is deliberately not asserted by this value theorem. -/
theorem on_run {CoreError H : Type} (installed : AspisR1CurrentCaller.Ops) (reserved : Bool)
    (query : Port3_NativeQueryBody.Ops) (geo : Port3_NativeGeometryBody.Ops CoreError)
    (D : AspisR1CurrentCaller.aspis_core.digest.Digest32 H) (hash : H)
    (semantic : AspisR1CurrentCaller.aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
    (pub proof : Slice U8) (split : Usize) (saved : alloc.vec.Vec U8)
    (run : Tx1Q_Execution.Run installed reserved query geo D hash semantic pub proof split saved)
    (owner : SessionAPrepare installed)
    (ports : Port5Q1_QueryPorts.SessionAPrimitives query)
    (proofLength : proof.val.length = 57607) (publicLength : pub.val.length = 1880) :
    Admitted (prepared run.p)
      (accumulator {run.out with weights := ⟨run.flushed.val,run.flushed.property⟩}) proof pub := by
  have fields := owner.accepted D hash semantic proof run.zero run.p run.scratch run.prepare_call
  have mutable := WAdm_Arithmetic.on_run installed reserved query geo D hash semantic pub proof split saved
    run ports fields.rho
  have control := Tx1Q_Control.fields installed reserved query geo D hash semantic pub proof split saved run
  refine ⟨fields.variant,?_,control.2.2.1,fields.gamma,fields.kappa,?_,fields.claim,
    mutable.1,proofLength,publicLength⟩
  · simpa only [accumulator,vec,List.length_map] using control.2.2.2.1
  · intro x member
    obtain ⟨i,hi,hx⟩ := List.getElem_of_mem member
    have bound : i < 2 := by simpa only [(prepared run.p).alpha.property] using hi
    have h := fields.alpha ⟨i,bound⟩
    rw [hx] at h
    exact h

#print axioms on_run
#print SessionAPrepare
#print Admitted
end AspisR1.WAdm_Domain
end
