import NDO_JGg_QueryWords0
import Query31ConcreteDriverTraceFacts
set_option autoImplicit false
namespace AspisR1.JGg_QueryScan0
open Aeneas Aeneas.Std Result
open Query31ExplicitListLoop Query31ExplicitScanBody AspisV8R19.Q22WordScan

theorem source  :
    ∃ sf,Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
      Query31ConcreteDriverTraceFacts.sourceDefaultState (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block0)=ok (false,sf) ∧
      validState sf ∧ q22StateOf sf=⟨[93499, 147529, 216823, 245899, 209371, 192317, 65593, 183859],8⟩ := by
  obtain ⟨sf,pending,loop,semantic,validFinal⟩ := scanListLoop_q22_valid JGg_QueryWords0.value.val Query31ConcreteDriverTraceFacts.sourceDefaultState Query31ConcreteDriverTraceFacts.sourceDefaultState_valid
  have numeric : scan (q22StateOf Query31ConcreteDriverTraceFacts.sourceDefaultState) (JGg_QueryWords0.value.val.map (fun x=>x.val))=
      (⟨[93499, 147529, 216823, 245899, 209371, 192317, 65593, 183859],8⟩,false) := by
    rw [Query31ConcreteDriverTraceFacts.sourceDefaultState_maps_to_empty_q22]
    rfl
  have same := semantic.symm.trans numeric
  have stateFinal := congrArg Prod.fst same
  have stopped := congrArg Prod.snd same
  refine ⟨sf,?_,validFinal,stateFinal⟩
  simp only [Query31ModelScanCall.modelScanFn,JGg_QueryWords0.source,bind_tc_ok,loop]
  exact congrArg (fun b => ok (b,sf)) stopped
#print axioms source
end AspisR1.JGg_QueryScan0
