import NDO_JGn_CopyRows
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGn_CopyChunk06
open JGn_CopyRows
theorem pv0 : (block06.foldl step row048).producerValues 0=row056.producerValues 0 := by
  jgl_words
#print axioms pv0
theorem pv1 : (block06.foldl step row048).producerValues 1=row056.producerValues 1 := by
  jgl_words
#print axioms pv1
theorem pw0 : (block06.foldl step row048).producerWeights 0=row056.producerWeights 0 := by
  jgl_words
#print axioms pw0
theorem pw1 : (block06.foldl step row048).producerWeights 1=row056.producerWeights 1 := by
  jgl_words
#print axioms pw1
theorem cv0 : (block06.foldl step row048).consumerValues 0=row056.consumerValues 0 := by
  jgl_words
#print axioms cv0
theorem cv1 : (block06.foldl step row048).consumerValues 1=row056.consumerValues 1 := by
  jgl_words
#print axioms cv1
theorem cw0 : (block06.foldl step row048).consumerWeights 0=row056.consumerWeights 0 := by
  jgl_words
#print axioms cw0
theorem cw1 : (block06.foldl step row048).consumerWeights 1=row056.consumerWeights 1 := by
  jgl_words
#print axioms cw1
theorem value : block06.foldl step row048=row056 := by
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
end AspisR1.JGn_CopyChunk06
end
