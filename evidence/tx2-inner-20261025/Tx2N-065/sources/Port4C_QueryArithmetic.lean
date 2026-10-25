import Port4C_QueryValues

/-! Primitive S3/S4/S5/S9 backend ports remain session A hypotheses. They
mention only the primitive's actual operands/result, not a query, accepted
transaction, trace or desired advance law. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.Port4C_QueryArithmetic
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port3_NativeQueryBody Port4C_QueryValues
open CheckpointBytes5Output (ofE ofK)
abbrev FK := OraclePortCheckpointAbiC5.K
abbrev FE := OraclePortCheckpointAbiC5.E

def CanonE (x : E) : Prop :=
  Port3_FlushInstall.Canonical x.c0 ∧ Port3_FlushInstall.Canonical x.c1

structure SessionABackends (ops : Ops) : Prop where
  s3_s4_s5_mulE : ∀ value power product,
    CanonE value → Port3_FlushInstall.Canonical power →
    ops.op3 value power=ok product →
    ofE product=ofE value * LiteralOpeningView.eK (ofK power) ∧ CanonE product
  s3_s4_s5_addE : ∀ left right sum,
    CanonE left → CanonE right → ops.op2 left right=ok sum →
    ofE sum=ofE left+ofE right ∧ CanonE sum
  s3_s4_s9_mulK : ∀ left right product,
    Port3_FlushInstall.Canonical left → Port3_FlushInstall.Canonical right →
    ops.op9 left right=ok product →
    ofK product=ofK left*ofK right ∧ Port3_FlushInstall.Canonical product

/-- The output rhs/power are decoded from the SAME native accumulation.
The row updates stay in pending until flush, so this does not assert that the
unflushed physical weights have already changed. -/
theorem accumulation (ops : Ops) (backend : SessionABackends ops)
    (p : verifier.Prepared) (a out : verifier.Accumulator) (node : M) (value : E)
    (b bout : verifier.BatchedWeights)
    (hp : Port3_FlushInstall.Canonical a.power)
    (hrho : Port3_FlushInstall.Canonical p.rho) (hrhs : CanonE a.rhs)
    (hv : CanonE value)
    (h : verifier.accumulate_batched_with_node ops p a node value b=ok (out,bout)) :
    ofE out.rhs=ofE a.rhs+LiteralOpeningView.eK (ofK a.power)*ofE value ∧
    ofK out.power=ofK a.power*ofK p.rho ∧ CanonE out.rhs ∧
    Port3_FlushInstall.Canonical out.power := by
  obtain ⟨product,hprod,hadd,hmul,_,_⟩ := Port4C_QueryValues.accumulated ops p a out node value b bout h
  have product := backend.s3_s4_s5_mulE value a.power product hv hp hprod
  have sum := backend.s3_s4_s5_addE a.rhs _ out.rhs hrhs product.2 hadd
  have power := backend.s3_s4_s9_mulK a.power p.rho out.power hp hrho hmul
  refine ⟨?_,power.1,sum.2,power.2⟩
  rw [sum.1,product.1,mul_comm]

/-- Opening/fold/geometry observations are derived from this call. A caller
may instantiate the line-value interpretation on precisely that observation.
There is no separately supplied successful opening or accumulation. -/
theorem query (ops : Ops) (backend : SessionABackends ops)
    (proof : Slice U8) (p : verifier.Prepared) (a out : verifier.Accumulator)
    (g : Array E 29#usize) (obs : Option (verifier.Phase → Result Unit))
    (geometry : verifier.QueryGeometry) (b bout : verifier.BatchedWeights)
    (hp : Port3_FlushInstall.Canonical a.power)
    (hrho : Port3_FlushInstall.Canonical p.rho) (hrhs : CanonE a.rhs)
    (line_canonical : ∀ alpha values inverses value,
      ops.op16 alpha values inverses=ok value → CanonE value)
    (h : verifier.candidate.query_values ops proof p a g obs geometry b=ok (.Ok (out,bout))) :
    ∃ o : Observation ops proof p a out g obs geometry b bout,
      ofE out.rhs=ofE a.rhs+LiteralOpeningView.eK (ofK a.power)*ofE o.value ∧
      ofK out.power=ofK a.power*ofK p.rho ∧ out.next.val=a.next.val+1 ∧
      out.weights=a.weights ∧ CanonE out.rhs ∧ Port3_FlushInstall.Canonical out.power := by
  obtain ⟨o⟩ := Port4C_QueryValues.observed ops proof p a out g obs geometry b bout h
  have fields := Port3_NativeQueryFrame.query_fields ops proof p a out g obs geometry b bout h
  have arithmetic := accumulation ops backend p a out o.node o.value b bout hp hrho hrhs
    (line_canonical o.alpha1 o.values o.inverse o.value o.line) o.accumulate
  exact ⟨o,arithmetic.1,arithmetic.2.1,fields.2.2,fields.2.1,arithmetic.2.2⟩

#print axioms accumulation
#print axioms query
end AspisR1.Port4C_QueryArithmetic
end
