import NDO_JHk_PreparedRemaining
import NDO_JHn_Ranges
set_option autoImplicit false
namespace AspisR1.JHn_QueryRanges
open Aeneas Aeneas.Std
attribute [local irreducible] JFx_NativeBytes.checkpoint JFx_NativeBytes.checkpointBytes
theorem source : JFq_QueryWords.b0.val ++ JFq_QueryWords.b1.val ++ JFq_QueryWords.b2.val ++ JFq_QueryWords.b3.val ++ JFq_QueryWords.b4.val ++ JFq_QueryWords.b5.val ++ JFq_QueryWords.b6.val ++ JFq_QueryWords.b7.val ++ JFq_QueryWords.b8.val ++ JFq_QueryWords.b9.val ++ JFq_QueryWords.b10.val ++ JFq_QueryWords.b11.val ++ JFq_QueryWords.b12.val ++ JFq_QueryWords.b13.val ++ JFq_QueryWords.b14.val ++ JFq_QueryWords.b15.val ++ JFq_QueryWords.b16.val ++ JFq_QueryWords.b17.val ++ JFq_QueryWords.b18.val ++ JFq_QueryWords.b19.val ++ JFq_QueryWords.b20.val ++ JFq_QueryWords.b21.val =
    (JFx_NativeBytes.checkpoint.val.drop 320).take 88 := by
  rw [←JFq_QueryWords.select0,←JFq_QueryWords.select1,←JFq_QueryWords.select2,←JFq_QueryWords.select3,←JFq_QueryWords.select4,←JFq_QueryWords.select5,←JFq_QueryWords.select6,←JFq_QueryWords.select7,←JFq_QueryWords.select8,←JFq_QueryWords.select9,←JFq_QueryWords.select10,←JFq_QueryWords.select11,←JFq_QueryWords.select12,←JFq_QueryWords.select13,←JFq_QueryWords.select14,←JFq_QueryWords.select15,←JFq_QueryWords.select16,←JFq_QueryWords.select17,←JFq_QueryWords.select18,←JFq_QueryWords.select19,←JFq_QueryWords.select20,←JFq_QueryWords.select21]
  rw [JHn_Ranges.adjacent _ 320 4 4,JHn_Ranges.adjacent _ 320 8 4,JHn_Ranges.adjacent _ 320 12 4,JHn_Ranges.adjacent _ 320 16 4,JHn_Ranges.adjacent _ 320 20 4,JHn_Ranges.adjacent _ 320 24 4,JHn_Ranges.adjacent _ 320 28 4,JHn_Ranges.adjacent _ 320 32 4,JHn_Ranges.adjacent _ 320 36 4,JHn_Ranges.adjacent _ 320 40 4,JHn_Ranges.adjacent _ 320 44 4,JHn_Ranges.adjacent _ 320 48 4,JHn_Ranges.adjacent _ 320 52 4,JHn_Ranges.adjacent _ 320 56 4,JHn_Ranges.adjacent _ 320 60 4,JHn_Ranges.adjacent _ 320 64 4,JHn_Ranges.adjacent _ 320 68 4,JHn_Ranges.adjacent _ 320 72 4,JHn_Ranges.adjacent _ 320 76 4,JHn_Ranges.adjacent _ 320 80 4,JHn_Ranges.adjacent _ 320 84 4]
#print axioms source
end AspisR1.JHn_QueryRanges
