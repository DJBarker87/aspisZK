import NDO_JGn_CopyRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyChunk16
open JGn_CopyRows
theorem pv0 : (block16.foldl step row128).producerValues 0=row136.producerValues 0 := by
  jgl_words
#print axioms pv0
theorem pv1 : (block16.foldl step row128).producerValues 1=row136.producerValues 1 := by
  jgl_words
#print axioms pv1
theorem pw0 : (block16.foldl step row128).producerWeights 0=row136.producerWeights 0 := by
  jgl_words
#print axioms pw0
theorem pw1 : (block16.foldl step row128).producerWeights 1=row136.producerWeights 1 := by
  jgl_words
#print axioms pw1
theorem cv0 : (block16.foldl step row128).consumerValues 0=row136.consumerValues 0 := by
  jgl_words
#print axioms cv0
theorem cv1 : (block16.foldl step row128).consumerValues 1=row136.consumerValues 1 := by
  jgl_words
#print axioms cv1
theorem cw0 : (block16.foldl step row128).consumerWeights 0=row136.consumerWeights 0 := by
  jgl_words
#print axioms cw0
theorem cw1 : (block16.foldl step row128).consumerWeights 1=row136.consumerWeights 1 := by
  jgl_words
#print axioms cw1
theorem value : block16.foldl step row128=row136 := by
  apply JGn_CopyRows.ext
  · funext i
    fin_cases i
    · exact pv0
    · exact pv1
  · funext i
    fin_cases i
    · exact pw0
    · exact pw1
  · funext i
    fin_cases i
    · exact cv0
    · exact cv1
  · funext i
    fin_cases i
    · exact cw0
    · exact cw1
#print axioms value
end AspisR1.JGn_CopyChunk16
end
