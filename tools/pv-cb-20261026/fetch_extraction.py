"""Fetch a complete extraction and record the import-only adaptation."""
from pathlib import Path
import subprocess,json,hashlib,sys,re
n=sys.argv[1];root=Path(__file__).resolve().parents[2]
dst=root/'docs/research/v8-r0-zk-20261009/lean/R1Z'
base=f'dombarker@100.108.41.90:/home/dombarker/project-offloads/codex-pv-cb-20261026/shipped-op{n}-generated/'
raw={};shift_adaptations=[];logical_tag_adapter=False
for kind in ['Types','Funs']:
 p=dst/f'PV_CB_Op{n}{kind}.lean';assert not p.exists(),str(p)
 subprocess.run(['scp',base+kind+'.lean',str(p)],check=True)
 s=p.read_text();raw[kind]=hashlib.sha256(s.encode()).hexdigest()
 if kind=='Funs':
  assert 'FunsExternal' not in s,'Opaque external functions: cannot install source law'
  s=s.replace(f'import PVCBShippedOp{n}.Types',f'import R1Z.PV_CB_Op{n}Types')
  if 'Option' in s and 'read_discriminant' in s:
   s=s.replace('import Aeneas\n','import Aeneas\nimport R1Z.PV_CB_OptionDiscriminant\n',1)
   logical_tag_adapter=True
  def shift(match):
   count=int(match[2]);assert count<2**32
   replacement=match[1]+match[2]+'#u32'
   shift_adaptations.append(dict(before=match[0],after=replacement))
   return replacement
  s=re.sub(r'(\b(?:Std\.)?U(?:8|16|32|64|128|size)\.wrapping_shr [A-Za-z_][\w.]* )(\d+)#i32\b',shift,s)
  p.write_text(s)
r=dict(raw_sha256=raw,shift_count_type_adaptations=shift_adaptations,logical_option_tag_adapter=logical_tag_adapter,change='Funs imports rewritten to own Types and, for emitted Option residual discriminant checks, the proved None0/Some1 adapter; nonnegative wrapping_shr literal counts rendered U32 for the pinned backend API, preserving numeric amounts; all other emitted bodies and Types unchanged; no external function template.')
(root/f'evidence/pv-cb-20261026/op{n}-normalization.json').write_text(json.dumps(r,indent=2)+'\n')
