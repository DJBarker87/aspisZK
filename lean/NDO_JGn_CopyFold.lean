import NDO_JGn_CopyChunk00
import NDO_JGn_CopyChunk01
import NDO_JGn_CopyChunk02
import NDO_JGn_CopyChunk03
import NDO_JGn_CopyChunk04
import NDO_JGn_CopyChunk05
import NDO_JGn_CopyChunk06
import NDO_JGn_CopyChunk07
import NDO_JGn_CopyChunk08
import NDO_JGn_CopyChunk09
import NDO_JGn_CopyChunk10
import NDO_JGn_CopyChunk11
import NDO_JGn_CopyChunk12
import NDO_JGn_CopyChunk13
import NDO_JGn_CopyChunk14
import NDO_JGn_CopyChunk15
import NDO_JGn_CopyChunk16
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyFold
open Aeneas Aeneas.Std FIq_Native
open JGn_CopyRows
attribute [local irreducible] List.foldl FJk_CopyStep.step R0P.copyLinks

theorem value : FJk_CopyFullFold.model JGl_NumericData.selectors JGn_CopyData.patterns
    JFu_PublicSemantic.value.transition.live_snapshot.next_pair_index
    pool_v1.pair_forest_copy_terminal.PoolV1PairForestCompiledVariantV1.PrivateTransfer=row136 := by
  have layout : R0P.copyLinks=block00++block01++block02++block03++block04++block05++block06++block07++block08++block09++block10++block11++block12++block13++block14++block15++block16 := by
    unfold block00 block01 block02 block03 block04 block05 block06 block07 block08 block09 block10 block11 block12 block13 block14 block15 block16 R0P.copyLinks
    rfl
  have initial : FJk_CopyFullFold.initial=row000 := by
    apply JGn_CopyRows.ext <;> funext i <;> fin_cases i <;> rfl
  unfold FJk_CopyFullFold.model
  rw [initial]
  change R0P.copyLinks.foldl step row000=row136
  rw [layout]
  simp only [List.foldl_append]
  rw [JGn_CopyChunk00.value,JGn_CopyChunk01.value,JGn_CopyChunk02.value,JGn_CopyChunk03.value,
    JGn_CopyChunk04.value,JGn_CopyChunk05.value,JGn_CopyChunk06.value,JGn_CopyChunk07.value,
    JGn_CopyChunk08.value,JGn_CopyChunk09.value,JGn_CopyChunk10.value,JGn_CopyChunk11.value,
    JGn_CopyChunk12.value,JGn_CopyChunk13.value,JGn_CopyChunk14.value,JGn_CopyChunk15.value,
    JGn_CopyChunk16.value]
#print axioms value
end AspisR1.JGn_CopyFold
end
