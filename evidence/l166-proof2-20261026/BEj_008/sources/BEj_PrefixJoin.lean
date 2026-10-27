import BEj_SlotExport
set_option autoImplicit false
namespace AspisR1.BEj_PrefixJoin
open Aeneas Aeneas.Std Result SdkC_Source

/-- Recorder cuts compose chronologically with an explicit intervening
segment. This cannot identify a batch segment with the headline recorder. -/
theorem chronological (before first second final between : Log)
    (cut0 : first = before ++ BEi_RecorderCut.issued before first)
    (middle : second = first ++ between)
    (cut1 : final = second ++ BEi_RecorderCut.issued second final) :
    final = before ++ BEi_RecorderCut.issued before first ++ between ++
      BEi_RecorderCut.issued second final := by
  rw [cut1,middle,cut0]

/-- Shared prefix occurrences are never deduplicated. The combined local
batch charge is 1800; no bound on intervening calls is invented. -/
theorem length_bound (before first second final between : Log)
    (cut0 : first = before ++ BEi_RecorderCut.issued before first)
    (middle : second = first ++ between)
    (cut1 : final = second ++ BEi_RecorderCut.issued second final)
    (bound0 : (BEi_RecorderCut.issued before first).length ≤ 900)
    (bound1 : (BEi_RecorderCut.issued second final).length ≤ 900) :
    final.length ≤ before.length + between.length + 1800 := by
  rw [chronological before first second final between cut0 middle cut1]
  simp only [List.length_append]
  omega

#print axioms chronological
#print axioms length_bound
end AspisR1.BEj_PrefixJoin
