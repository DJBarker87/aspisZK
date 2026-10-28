import NDO_JGn_CopyRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyChunk02
open JGn_CopyRows
theorem pv0 : (block02.foldl step row016).producerValues 0=row024.producerValues 0 := by
  jgl_words
#print axioms pv0
theorem pv1 : (block02.foldl step row016).producerValues 1=row024.producerValues 1 := by
  jgl_words
#print axioms pv1
theorem pw0 : (block02.foldl step row016).producerWeights 0=row024.producerWeights 0 := by
  jgl_words
#print axioms pw0
theorem pw1 : (block02.foldl step row016).producerWeights 1=row024.producerWeights 1 := by
  jgl_words
#print axioms pw1
theorem cv0 : (block02.foldl step row016).consumerValues 0=row024.consumerValues 0 := by
  jgl_words
#print axioms cv0
theorem cv1 : (block02.foldl step row016).consumerValues 1=row024.consumerValues 1 := by
  jgl_words
#print axioms cv1
theorem cw0 : (block02.foldl step row016).consumerWeights 0=row024.consumerWeights 0 := by
  jgl_words
#print axioms cw0
theorem cw1 : (block02.foldl step row016).consumerWeights 1=row024.consumerWeights 1 := by
  jgl_words
#print axioms cw1
theorem value : block02.foldl step row016=row024 := by
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
end AspisR1.JGn_CopyChunk02
end
