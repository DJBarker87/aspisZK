import NDO_JGg_QueryWords1
import Query31ConcreteDriverTraceFacts
set_option autoImplicit false
namespace AspisR1.JGg_QueryScan1
open Aeneas Aeneas.Std Result
open Query31ExplicitListLoop Query31ExplicitScanBody AspisV8R19.Q22WordScan

theorem source (s : Query31ModelDriverChain.QueryScan) (valid : validState s)
    (state : q22StateOf s=⟨[93499, 147529, 216823, 245899, 209371, 192317, 65593, 183859],8⟩) :
    ∃ sf,Query31ModelScanCall.modelScanFn Query31ConcreteWordsDriverChain.actualQueryWords
      s (AspisV8R19.SqueezeOracleBridge.encodeState JGg_Opening31.block1)=ok (false,sf) ∧
      validState sf ∧ q22StateOf sf=⟨[93499, 147529, 216823, 245899, 209371, 192317, 65593, 183859, 193093, 159813, 132355, 218094, 178080, 149624, 166165, 42158],16⟩ := by
  obtain ⟨sf,pending,loop,semantic,validFinal⟩ := scanListLoop_q22_valid JGg_QueryWords1.value.val s valid
  have numeric : scan (q22StateOf s) (JGg_QueryWords1.value.val.map (fun x=>x.val))=
      (⟨[93499, 147529, 216823, 245899, 209371, 192317, 65593, 183859, 193093, 159813, 132355, 218094, 178080, 149624, 166165, 42158],16⟩,false) := by
    rw [state]
    rfl
  have same := semantic.symm.trans numeric
  have stateFinal := congrArg Prod.fst same
  have stopped := congrArg Prod.snd same
  refine ⟨sf,?_,validFinal,stateFinal⟩
  simp only [Query31ModelScanCall.modelScanFn,JGg_QueryWords1.source,bind_tc_ok,loop]
  exact congrArg (fun b => ok (b,sf)) stopped
#print axioms source
end AspisR1.JGg_QueryScan1
