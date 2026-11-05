from pathlib import Path
E=Path(__file__).resolve().parent;p=E/'NHQ_FinishRelationModel.lean'
s=(E/'NHQ_FinishNormal.unproved.lean.txt').read_text()
raw=(E.parent/'slice-d-finish-20261105/NGM_FinishControl.lean').read_text()
a=raw.index('def run (ops : Ops W)');b=raw.index('/-- Complete source Result',a);body=raw[a:b].replace('def run (ops : Ops W)','def staged (ops : Ops W)')
# Keep source-shaped matches; avoid repeated broad normalization across 6 continuations.
a=s.index('def staged');b=s.index('/-- The pair',a)
s=s[:a]+body+'''theorem source (ops : Ops W) (v : verifier.View) (p : verifier.Prepared)
 (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit)) :
 Port3_NativeFinishBody.verifier.finish_relation ops v p a obs = staged ops v p a obs := by rfl

'''+s[b:]
p.write_text(s)
