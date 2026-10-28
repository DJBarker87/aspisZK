import NDO_JGn_CopyData
import RPv_FJk_PatternRegistry
import NDO_JGl_WordProof
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_PatternMath
open FIw_ArrayValue (decoded)
theorem lane0 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨0,by decide⟩=
    decoded JGn_CopyData.patterns ⟨0,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane0
theorem lane1 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨1,by decide⟩=
    decoded JGn_CopyData.patterns ⟨1,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane1
theorem lane2 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨2,by decide⟩=
    decoded JGn_CopyData.patterns ⟨2,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane2
theorem lane3 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨3,by decide⟩=
    decoded JGn_CopyData.patterns ⟨3,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane3
theorem lane4 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨4,by decide⟩=
    decoded JGn_CopyData.patterns ⟨4,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane4
theorem lane5 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨5,by decide⟩=
    decoded JGn_CopyData.patterns ⟨5,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane5
theorem lane6 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨6,by decide⟩=
    decoded JGn_CopyData.patterns ⟨6,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane6
theorem lane7 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨7,by decide⟩=
    decoded JGn_CopyData.patterns ⟨7,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane7
theorem lane8 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨8,by decide⟩=
    decoded JGn_CopyData.patterns ⟨8,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane8
theorem lane9 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨9,by decide⟩=
    decoded JGn_CopyData.patterns ⟨9,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane9
theorem lane10 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨10,by decide⟩=
    decoded JGn_CopyData.patterns ⟨10,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane10
theorem lane11 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨11,by decide⟩=
    decoded JGn_CopyData.patterns ⟨11,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane11
theorem lane12 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨12,by decide⟩=
    decoded JGn_CopyData.patterns ⟨12,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane12
theorem lane13 : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers ⟨13,by decide⟩=
    decoded JGn_CopyData.patterns ⟨13,by decide⟩ := by
  unfold FJk_PatternOuterValue.model
  rw [FJk_PatternRegistry.value]
  jgl_words
#print axioms lane13
theorem value : FJk_PatternOuterValue.model JGl_NumericData.a JGn_CopyPowers.powers=
    decoded JGn_CopyData.patterns := by
  funext i
  fin_cases i
  · exact lane0
  · exact lane1
  · exact lane2
  · exact lane3
  · exact lane4
  · exact lane5
  · exact lane6
  · exact lane7
  · exact lane8
  · exact lane9
  · exact lane10
  · exact lane11
  · exact lane12
  · exact lane13
#print axioms value
end AspisR1.JGn_PatternMath
end
