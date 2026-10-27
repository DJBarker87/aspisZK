"""Bind the single native-checked canonical helper; reject any extra hole."""
from pathlib import Path
import hashlib,json,re,subprocess
root=Path(__file__).resolve().parents[2]
lean=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
base='/home/dombarker/project-offloads/codex-pv-cb-20261026/shipped-op109-generated/'
def read(name):
 return subprocess.check_output(['ssh','dombarker@100.108.41.90','cat',base+name],text=True)
template=read('FunsExternal_Template.lean')
assert re.findall(r'^axiom\s+([\w.]+)',template,re.M)==['aspis_core.field.wide_exact.canonical_qm31']
assert re.search(r':\s*aspis_core.field.QM31\s*→\s*Result aspis_core.field.QM31\s*$',template)
raw_types=read('Types.lean');raw_funs=read('Funs.lean')
types_path=lean/'PV_CB_Op109Types.lean';funs_path=lean/'PV_CB_Op109Funs.lean'
assert not types_path.exists() and not funs_path.exists()
types_path.write_text(raw_types)
funs=raw_funs.replace('import PVCBShippedOp109.Types','import R1Z.PV_CB_Op109Types')
assert funs.count('import PVCBShippedOp109.FunsExternal')==1
funs=funs.replace('import PVCBShippedOp109.FunsExternal','import R1Z.PV_CB_Op109CanonicalBinding')
tag='Option' in funs and 'read_discriminant' in funs
if tag:funs=funs.replace('import Aeneas\n','import Aeneas\nimport R1Z.PV_CB_OptionDiscriminant\n',1)
changes=[]
def shift(m):
 assert int(m[2])<2**32
 after=m[1]+m[2]+'#u32';changes.append(dict(before=m[0],after=after));return after
funs=re.sub(r'(\b(?:Std\.)?U(?:8|16|32|64|128|size)\.wrapping_shr [A-Za-z_][\w.]* )(\d+)#i32\b',shift,funs)
assert 'FunsExternal' not in funs
assert not re.search(r'^\s*(axiom|opaque)\s|\b(sorry|admit|native_decide|implemented_by)\b',funs,re.M)
restored=funs
for change in changes:restored=restored.replace(change['after'],change['before'])
if tag:restored=restored.replace('import R1Z.PV_CB_OptionDiscriminant\n','')
restored=restored.replace('import R1Z.PV_CB_Op109Types','import PVCBShippedOp109.Types')
restored=restored.replace('import R1Z.PV_CB_Op109CanonicalBinding','import PVCBShippedOp109.FunsExternal')
assert restored==raw_funs
funs_path.write_text(funs)
sha=lambda s:hashlib.sha256(s.encode()).hexdigest()
report=dict(raw_sha256=dict(Types=sha(raw_types),Funs=sha(raw_funs)),external_template_sha256=sha(template),external_template_imported=False,external_declarations=['aspis_core.field.wide_exact.canonical_qm31'],concrete_binding='R1Z.PV_CB_Op109CanonicalBinding',reference_extraction='op109Ref',native_gate='kani-resume3-wide-new-002',logical_option_tag_adapter=tag,shift_count_type_adaptations=changes,all_other_emitted_bytes_preserved=True,status='P6 binding PREPARED; Types/codecs/reference/binding/Funs/Exact must compile before row discharge')
(root/'evidence/pv-cb-20261026/op109-normalization.json').write_text(json.dumps(report,indent=2)+'\n')
