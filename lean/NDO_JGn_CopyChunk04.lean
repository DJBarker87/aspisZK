import NDO_JGn_CopyRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyChunk04
open JGn_CopyRows
theorem pv0 : (block04.foldl step row032).producerValues 0=row040.producerValues 0 := by
  jgl_words
#print axioms pv0
theorem pv1 : (block04.foldl step row032).producerValues 1=row040.producerValues 1 := by
  jgl_words
#print axioms pv1
theorem pw0 : (block04.foldl step row032).producerWeights 0=row040.producerWeights 0 := by
  jgl_words
#print axioms pw0
theorem pw1 : (block04.foldl step row032).producerWeights 1=row040.producerWeights 1 := by
  jgl_words
#print axioms pw1
theorem cv0 : (block04.foldl step row032).consumerValues 0=row040.consumerValues 0 := by
  jgl_words
#print axioms cv0
theorem cv1 : (block04.foldl step row032).consumerValues 1=row040.consumerValues 1 := by
  jgl_words
#print axioms cv1
theorem cw0 : (block04.foldl step row032).consumerWeights 0=row040.consumerWeights 0 := by
  jgl_words
#print axioms cw0
theorem cw1 : (block04.foldl step row032).consumerWeights 1=row040.consumerWeights 1 := by
  jgl_words
#print axioms cw1
theorem value : block04.foldl step row032=row040 := by
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
end AspisR1.JGn_CopyChunk04
end
