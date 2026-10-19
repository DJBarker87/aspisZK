from pathlib import Path
import re
p=Path(__file__).resolve().parent
raw=(p/'extraction/generated-Funs.lean').read_text()
raw=raw.replace('import AspisR1Stage2AdoptedCaller.FunsExternal\n','')
raw=re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',raw,flags=re.M)
body=(p/'sources/Stage2AuthExplicitBoundaries.lean').read_text()
a=body.index('/-- Explicit universally quantified boundaries')
z=body.index('/-- [aspis_r1_stage2_adopted_caller::verifier::mark]')
body=body[:a]+body[z:]
raw=raw.replace('{H : Type} (aspis_coreDigest32Inst : aspis_core.Digest32 H)','{H : Type} (boundaries : Stage2AuthBoundaries H) (aspis_coreDigest32Inst : aspis_core.Digest32 H)')
raw=raw.replace('let r ← verifier.candidate.parse_shape proof','let r ← boundaries.parse_shape proof').replace('    verifier.candidate.tx2_common aspis_coreDigest32Inst','    boundaries.tx2_common aspis_coreDigest32Inst')
assert raw.split()==body.split(),'Body differs beyond explicit boundary elaboration adapter'
t=(p/'extraction/generated-Types.lean').read_text();t=re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',t,flags=re.M)
assert t==(p/'sources/AspisR1Stage2AdoptedCaller/Types.lean').read_text()
print('Checked unchanged generated bodies under explicit boundary parameterization; no resource overrides')
