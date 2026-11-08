import PV_LIB_A_Continuation12
import PV_LIB_A_ChainTrace11
import PV_THR2_IntrinsicFrameAggregate
import PV_LIB_A_F6EarlyHistory11
set_option autoImplicit false
noncomputable section
namespace PV_LIB_A_F6Data12
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_EVHB_OwnerMachine PV_EVHB_OwnerHeap PV_THR2_SourceStoreLibrary
open PV_LIB_StoreActionTable PV_LIB_A_PrefixMachine11

/-- Read aggregate metadata and operands from actual1876. -/
def source : PV_STX2_Syntax.Site × PV_STX2_Syntax.Place × Data × List Operand := match PV_THR2_F6.node21 with
  | .leaf (.aggregateMove site dest kind args) => (site,dest,kind,args)
  | _ => (⟨0,0,.null⟩,.local 0,.null,[])

def finish (C : Carrier OWNER Data) (c : Config) (w : OWNER)
    (es : List PV_RJ4IDB.NativeEvent) (stack : List Config) :=
  PV_THR2_IntrinsicFrameAggregate.after C c.store c.frame.activation c.callers c.frame.loops
    (PV_THR2_F6.live.body.drop 22) source.1 source.2.1 source.2.2.1 source.2.2.2 w es stack

def steps (q : State) := PV_THR2_IntrinsicAtContinuation.steps
  (PV_THR2_F6.live.body.drop 21) (fun _ _ => 1) q

def after (C : Carrier OWNER Data) (q : State) := PV_THR2_IntrinsicAtContinuation.after
  (PV_THR2_F6.live.body.drop 21) (finish C) q

theorem trace (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (H : Handler) (q : State) :
    Trace C K P H (steps q) q := by
  apply PV_LIB_A_Continuation12.trace
  intro c w es stack h
  rw [PV_THR2_IntrinsicAtContinuation.frame c h]
  refine ⟨?_,True.intro⟩
  constructor
  · intro c hc; cases hc; rfl
  · intro c hc; cases hc; exact ⟨rfl,rfl,True.intro⟩

/-- The actual ScopeData aggregate on the corrected machine, retaining unknown
constructor payloads and all missing-cell cases; no decoder/value premise. -/
theorem run (C : Carrier OWNER Data) (K : Control)
    (P : Data → Option PV_STX2_SliceSyntax.Program) (resources : Resources) (encode : Encode)
    (H : Handler) (values : Values OWNER PV_RJ4IDB.NativeEvent) (q : State) :
    advance C K P resources encode H values (steps q) ⟨q,none⟩ = ⟨after C q,none⟩ := by
  rw [PV_LIB_A_PrefixMachine11.run C K P resources encode H values _ _ (trace C K P H q)]
  apply congrArg (fun q => (⟨q,none⟩ : SourceState))
  apply PV_THR2_IntrinsicAtContinuation.run
  intro c w es stack h
  rcases c with ⟨⟨a,rest,loops,wait,unwind,done⟩,parents,s⟩
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  change PV_THR2_IntrinsicState.advance C K P H 1
    ⟨⟨.running ⟨{activation := a,remaining := PV_THR2_F6.node21 :: PV_THR2_F6.live.body.drop 22,loops := loops},parents,s⟩,w,es⟩,stack⟩ = _
  exact PV_THR2_IntrinsicFrameAggregate.run C K P H s a parents loops _
    source.1 source.2.1 source.2.2.1 source.2.2.2 w es stack

#print axioms source
#print axioms finish
#print axioms steps
#print axioms after
#print axioms trace
#print axioms run
end PV_LIB_A_F6Data12
