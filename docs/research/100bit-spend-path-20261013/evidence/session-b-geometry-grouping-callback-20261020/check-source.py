from pathlib import Path
import hashlib,json,re,subprocess
p=Path(__file__).resolve().parent
j=json.loads((p/'extraction/input/source-pins.json').read_text())
h=lambda b:hashlib.sha256(b).hexdigest()
for n,pin in j['kit_files'].items():assert h((p/'extraction/input'/n).read_bytes())==pin
for c in j['cuts']:
 raw=subprocess.check_output(['git','show',j['revision']+':'+c['path']]);frag=(p/'extraction/input/fragments'/(c['name']+'.rs')).read_bytes();assert raw[c['start_byte']:c['end_byte_exclusive']]==frag;assert h(frag)==c['sha256']
r=p/'extraction/generated/AspisR1GeometryGrouping'
s=(r/'Funs.lean').read_text();a=s.index('/-- [aspis_r1_stage2_adopted_caller::geometry_groups::closure::{impl');z=s.index('/-- [aspis_r1_stage2_adopted_caller::geometry_groups::{impl',a)
out='import AspisR1GeometryGrouping.Types\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option autoImplicit false\nnoncomputable section\nnamespace AspisR1GeometryGrouping\n\n'+s[a:z]+'end AspisR1GeometryGrouping\n'
assert out==(p/'sources/GeometryGroupingCallback.lean').read_text()
clean=lambda s:re.sub(r'^set_option (?:maxHeartbeats|maxRecDepth).*\n','',s,flags=re.M)
assert clean((r/'Types.lean').read_text())==(p/'sources/AspisR1GeometryGrouping/Types.lean').read_text()
print('exact frozen grouping expression and selected unchanged generated FnMut/FnOnce callback declarations: PASS')
print('Opaque map/from_fn/Map.next templates were not compiled; stdlib source correspondence remains OPEN.')
