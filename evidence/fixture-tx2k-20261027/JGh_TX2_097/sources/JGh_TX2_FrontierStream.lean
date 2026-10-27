import JGh_TX2_FrontierHeight17
import JGf_TX2_Sort
import JGf_TX2_Count0
import JGf_TX2_Count2
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_FrontierOrder
open Aeneas Aeneas.Std Result

def q := Port4B_KeyInstall.queries JFo_Prepared.value.queries

theorem tree0 : (OraclePortFrozenOrder.sortedPositions q 1 0).map
    (OraclePortSelectedDraft.index q 0)=JGf_TX2_Count0.indices00 := by rfl
#print axioms tree0

theorem tree1 : (OraclePortFrozenOrder.sortedPositions q 1 1).map
    (OraclePortSelectedDraft.index q 1)=JGf_TX2_Count0.indices00 := by rfl
#print axioms tree1

theorem tree2 : (OraclePortFrozenOrder.sortedPositions q 1 2).map
    (OraclePortSelectedDraft.index q 2)=JGf_TX2_Count2.indices00 := by rfl
#print axioms tree2

theorem source (kind : Nat) : ∃ out : Array U64 16#usize,
    Port4B_Install.leaves.op5 (JGf_TX2_Keys.raw kind) 12#usize=ok out ∧
    Port4B_LeafLoop.KeyStream q 1 kind out 0#usize
      (OraclePortFrozenOrder.sortedPositions q 1 kind) := by
  obtain ⟨out,run,_front,_suffix⟩ := JGf_TX2_Sort.source kind
  refine ⟨out,run,?_⟩
  exact (Port4B_SortInstall.key_stream Port4B_Install.leaves q 1 kind
    (JGf_TX2_Keys.raw kind) out 12#usize (by decide) (by decide)
    (JGf_TX2_Keys.prefix_keys kind) run).2
#print axioms source
end AspisR1.JGh_TX2_FrontierOrder
end
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGh_TX2_Frontiers
open OraclePortSelectedDraft OracleDecisionMultiBuild
def stream0 : List (Nat×Nat) := [(0,14296),(0,21249),(0,42159),(0,55376),(0,63861),(0,132354),(0,149625),(0,166164),(0,178081),(0,179623),(0,185636),(0,218095),(1,14298),(1,21250),(1,42156),(1,55378),(1,63862),(1,132352),(1,149626),(1,166166),(1,178082),(1,179620),(1,185638),(1,218092),(2,14300),(2,21252),(2,42152),(2,55380),(2,63856),(2,132356),(2,149628),(2,166160),(2,178084),(2,179616),(2,185632),(2,218088),(3,14288),(3,21256),(3,42144),(3,55384),(3,63864),(3,132360),(3,149616),(3,166168),(3,178088),(3,179624),(3,185640),(3,218080),(4,14272),(4,21264),(4,42160),(4,55360),(4,63840),(4,132368),(4,149600),(4,166144),(4,178096),(4,179632),(4,185648),(4,218096),(5,14304),(5,21280),(5,42112),(5,55392),(5,63808),(5,132384),(5,149568),(5,166176),(5,178048),(5,179584),(5,185600),(5,218048),(6,14208),(6,21312),(6,42176),(6,55296),(6,63744),(6,132416),(6,149504),(6,166208),(6,178112),(6,179648),(6,185664),(6,217984),(7,14080),(7,21376),(7,41984),(7,55424),(7,63872),(7,132480),(7,149632),(7,166272),(7,177920),(7,179456),(7,185728),(7,217856),(8,13824),(8,20992),(8,42240),(8,55552),(8,63488),(8,132096),(8,149760),(8,165888),(8,177664),(8,179200),(8,185344),(8,217600),(9,13312),(9,20480),(9,42496),(9,55808),(9,64000),(9,132608),(9,150016),(9,166400),(9,177152),(9,179712),(9,185856),(9,217088),(10,12288),(10,21504),(10,40960),(10,56320),(10,64512),(10,131072),(10,150528),(10,166912),(10,176128),(10,178176),(10,184320),(10,218112),(11,14336),(11,22528),(11,43008),(11,53248),(11,61440),(11,133120),(11,147456),(11,163840),(11,186368),(11,219136),(12,8192),(12,16384),(12,45056),(12,49152),(12,57344),(12,135168),(12,151552),(12,167936),(12,172032),(12,180224),(12,212992),(13,0),(13,24576),(13,32768),(13,139264),(13,155648),(13,188416),(13,221184),(14,196608),(15,229376),(16,65536)]
theorem ordered0 : orderedFrontier JGf_TX2_M0Roots.indices=stream0 := by
  rw [orderedFrontier,front0_185]
  rfl
#print axioms ordered0
theorem count0 : MultiproofConeCountLevels.sourceCount 18 JGf_TX2_Count0.indices00=(orderedFrontier JGf_TX2_M0Roots.indices).length := by
  rw [JGf_TX2_Count0.total00,ordered0]
  rfl
#print axioms count0
theorem length0 : stream0.length=163 := rfl
#print axioms length0
def stream2 : List (Nat×Nat) := [(0,3575),(0,5313),(0,10538),(0,13845),(0,15964),(0,33089),(0,37407),(0,41540),(0,44521),(0,44904),(0,46408),(0,54522),(1,3572),(1,5314),(1,10536),(1,13846),(1,15966),(1,33090),(1,37404),(1,41542),(1,44522),(1,44906),(1,46410),(1,54520),(2,3568),(2,5316),(2,10540),(2,13840),(2,15960),(2,33092),(2,37400),(2,41536),(2,44524),(2,44908),(2,46412),(2,54524),(3,3576),(3,5320),(3,10528),(3,13848),(3,15952),(3,33096),(3,37392),(3,41544),(3,44512),(3,44896),(3,46400),(3,54512),(4,3552),(4,5328),(4,10544),(4,13824),(4,15936),(4,33104),(4,37376),(4,41552),(4,44528),(4,44912),(4,46416),(4,54496),(5,3520),(5,5344),(5,10496),(5,13856),(5,15968),(5,33120),(5,37408),(5,41568),(5,44480),(5,44864),(5,46432),(5,54464),(6,3456),(6,5248),(6,10560),(6,13888),(6,15872),(6,33024),(6,37440),(6,41472),(6,44416),(6,44800),(6,46336),(6,54400),(7,3328),(7,5120),(7,10624),(7,13952),(7,16000),(7,33152),(7,37504),(7,41600),(7,44288),(7,44928),(7,46464),(7,54272),(8,3072),(8,5376),(8,10240),(8,14080),(8,16128),(8,32768),(8,37632),(8,41728),(8,44032),(8,44544),(8,46080),(8,54528),(9,3584),(9,5632),(9,10752),(9,13312),(9,15360),(9,33280),(9,36864),(9,40960),(9,46592),(9,54784),(10,2048),(10,4096),(10,11264),(10,12288),(10,14336),(10,33792),(10,37888),(10,41984),(10,43008),(10,45056),(10,53248),(11,0),(11,6144),(11,8192),(11,34816),(11,38912),(11,47104),(11,55296),(12,49152),(13,57344),(14,16384),(16,65536),(17,131072)]
theorem ordered2 : orderedFrontier JGc_TX2_M2Roots.indices=stream2 := by
  rw [orderedFrontier,front2_163]
  rfl
#print axioms ordered2
theorem count2 : MultiproofConeCountLevels.sourceCount 18 JGf_TX2_Count2.indices00=(orderedFrontier JGc_TX2_M2Roots.indices).length := by
  rw [JGf_TX2_Count2.total00,ordered2]
  rfl
#print axioms count2
theorem length2 : stream2.length=141 := rfl
#print axioms length2
end AspisR1.JGh_TX2_Frontiers
end
