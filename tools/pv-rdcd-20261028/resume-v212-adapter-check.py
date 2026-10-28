"""Verify the historical adapter relation without writing regenerated output.
The original adapter is pinned JSON; each value correction has a named Lean law.
This is supplemental output typing validation, not a new original structural gate.
"""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd-20261028';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
p=R/'evidence/pv-cb-20261026/op107-normalization.json';original=json.loads(p.read_text())
assert subprocess.check_output(['git','show','af8459b3e3:'+str(p.relative_to(R))])==p.read_bytes()
def sha(b):return hashlib.sha256(b).hexdigest()
def tokens(s):
 s=s.split('\nnamespace ',1)[1].split('\n',1)[1].rsplit('\nend ',1)[0]
 s=re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S)
 return re.findall(r'"(?:[^"\\]|\\.)*"|\w+|[^\s]',s)
results=[]
for name in ['Types','Funs']:
 raw=(E/f'resume-v212-raw-{name}.lean.txt').read_bytes();retained=L/f'PV_CB_Op107{name}.lean';text=raw.decode();corrections=[]
 if name=='Funs':
  for delta in original['shift_count_type_adaptations']:
   assert text.count(delta['before'])==1,delta
   corrections.append(dict(**delta,law='R1Z.PV_RDCD_ShiftLiterals.shift'+('31' if '31#i32' in delta['before'] else '1')))
   text=text.replace(delta['before'],delta['after'])
 assert tokens(text)==tokens(retained.read_text()),name
 results.append(dict(kind=name,raw_sha256=sha(raw),retained_path=str(retained.relative_to(R)),retained_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(retained.relative_to(R))],text=True).strip(),retained_sha256=sha(retained.read_bytes()),baseline_blob=subprocess.check_output(['git','rev-parse','af8459b3e3:'+str(retained.relative_to(R))],text=True).strip(),tokens_equal_after_exact_recorded_adapter=True,typing_corrections=corrections))
out=dict(original_adapter_path=str(p.relative_to(R)),original_adapter_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(p.relative_to(R))],text=True).strip(),original_adapter_sha256=sha(p.read_bytes()),results=results,raw_output_modified=False,generated_authority_replaced=False,authority='existing tracked h5 retained PV_CB_Op107Types/Funs; exact historical adapter now separately proved; no h7 cohort gap',qualification='Raw unmodified elaboration41418 still fails and is not claimed passing. This relation validates the existing committed typing adapter against fresh extraction, not a replacement checker or a claim of an unmodified raw compile.')
(E/'resume-v212-adapter-check.json').write_text(json.dumps(out,indent=2)+'\n');print('Exact historical adapter validated for both files;3 literal corrections; no regenerated file written')
