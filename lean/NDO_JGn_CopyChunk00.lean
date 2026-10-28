import NDO_JGn_CopyRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyChunk00
open JGn_CopyRows
theorem pv0 : (block00.foldl step row000).producerValues 0=row008.producerValues 0 := by
  jgl_words
#print axioms pv0
theorem pv1 : (block00.foldl step row000).producerValues 1=row008.producerValues 1 := by
  jgl_words
#print axioms pv1
theorem pw0 : (block00.foldl step row000).producerWeights 0=row008.producerWeights 0 := by
  jgl_words
#print axioms pw0
theorem pw1 : (block00.foldl step row000).producerWeights 1=row008.producerWeights 1 := by
  jgl_words
#print axioms pw1
theorem cv0 : (block00.foldl step row000).consumerValues 0=row008.consumerValues 0 := by
  jgl_words
#print axioms cv0
theorem cv1 : (block00.foldl step row000).consumerValues 1=row008.consumerValues 1 := by
  jgl_words
#print axioms cv1
theorem cw0 : (block00.foldl step row000).consumerWeights 0=row008.consumerWeights 0 := by
  jgl_words
#print axioms cw0
theorem cw1 : (block00.foldl step row000).consumerWeights 1=row008.consumerWeights 1 := by
  jgl_words
#print axioms cw1
theorem value : block00.foldl step row000=row008 := by
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
end AspisR1.JGn_CopyChunk00
end
