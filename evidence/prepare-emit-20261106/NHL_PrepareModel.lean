import NHL_BufferFrame
import NHL_Packets
set_option autoImplicit false
noncomputable section
namespace AspisR1.NHL_PrepareModel
open Aeneas Aeneas.Std Result AspisR1CurrentCaller NHL_PrepareStages

theorem source_constants (base : Ops) (reserved : Bool) :
 ConcreteConstants.withConstants (NHL_Packets.installed base reserved)=
 NHL_Packets.installed base reserved := rfl

theorem target_constants (base expected : Ops) (reserved : Bool) :
 ConcreteConstants.withConstants (children (NHL_Packets.installed base reserved) expected)=
 children (NHL_Packets.installed base reserved) expected := rfl

/-- Exact preparation-prefix reachability, before either OPEN callee.
This is not a successful whole-prepare or selected final-output premise. -/
def Reaches (base : Ops) (reserved : Bool) {H : Type} (D : aspis_core.digest.Digest32 H)
 (proof : Slice U8) (v : verifier.View) : Prop :=
 buffers (NHL_Packets.installed base reserved) D proof=ok (.Ok v)

/-- Conditional full-body equality with CLOSED buffers/view installed.
Both hypotheses are needed only at an actual successful predecessor, with
SAME original arguments and full Result/post-scratch equality. -/
theorem source (base expected : Ops) (reserved : Bool) {H : Type}
 (D : aspis_core.digest.Digest32 H)
 (pub : aspis_statement.pool_v1.pair_forest_semantic_terminal.r0.Public)
 (proof : Slice U8) (hash : H) (g : Scratch)
 (verify_observed : ∀ v, Reaches base reserved D proof v →
   base.op9 D pub v.semantic hash none=expected.op9 D pub v.semantic hash none)
 (prepared_new : ∀ v sem, Reaches base reserved D proof v →
   expected.op9 D pub v.semantic hash none=ok (.Ok sem) →
   base.op8 D sem v hash g=expected.op8 D sem v hash g) :
 NHL_EmittedPrepare.prepare (NHL_Packets.installed base reserved) D pub proof hash none g=
 verifier.candidate.prepare (children (NHL_Packets.installed base reserved) expected)
   D pub proof hash none g := by
 have src := NHL_PrepareEq.source (NHL_Packets.installed base reserved) D pub proof hash none g
 have dst := NHL_PrepareEq.source (children (NHL_Packets.installed base reserved) expected) D pub proof hash none g
 rw [source_constants] at src
 rw [target_constants] at dst
 rw [←dst,NHL_PrepareStages.factor,NHL_PrepareStages.factor]
 unfold run
 rw [buffers_children]
 apply NHL_BindOn.reached
 intro reply prior
 cases reply with
 | Err e => rfl
 | Ok v =>
   simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]
   unfold semanticCut
   have reached : Reaches base reserved D proof v := prior
   change (do
     let r ← base.op9 D pub v.semantic hash none
     let mapped ← AspisR1CurrentCaller.core.result.Result.map_err
       (verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError D) r ()
     let cf ← core.result.Result.Insts.CoreOpsTry.branch mapped
     match cf with
     | .Continue sem => do
       verifier.mark none verifier.Phase.Semantic
       base.op8 D sem v hash g
     | .Break residual => do
       let e ← core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual
         verifier.Prepared (core.convert.FromSame verifier.Error) residual
       ok (e,g)) = _
   rw [verify_observed v reached]
   apply NHL_BindOn.reached
   intro semantic call
   cases semantic with
   | Err e => rfl
   | Ok sem =>
     simpa only [AspisR1CurrentCaller.core.result.Result.map_err,
       verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError,
       verifier.candidate.prepare.closure_1.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
       bind_tc_ok,core.result.Result.Insts.CoreOpsTry.branch,verifier.mark,children] using
       prepared_new v sem reached call
#print axioms source_constants
#print axioms target_constants
#print axioms source
end AspisR1.NHL_PrepareModel
