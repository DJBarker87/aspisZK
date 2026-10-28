"""Exact fresh/retained output relation under the committed original adapter."""
from pathlib import Path
import json,re,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd-20261028';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
def tok(s):
 s=s.split('\nnamespace ',1)[1].split('\n',1)[1].rsplit('\nend ',1)[0]
 return re.findall(r'"(?:[^"\\]|\\.)*"|\w+|[^\s]',re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S))
def sha(b):return hashlib.sha256(b).hexdigest()
p=R/'evidence/pv-cb-20261026/op118-normalization.json';a=json.loads(p.read_text());assert subprocess.check_output(['git','show','af8459b3e3:'+str(p.relative_to(R))])==p.read_bytes()
checks=[]
for kind in ['Types','Funs']:
 raw=E/f'resume-v218-generated-{kind}.lean.txt';s=raw.read_text();changes=[]
 if kind=='Funs':
  for d in a['shift_count_type_adaptations']:
   assert s.count(d['before'])==1;s=s.replace(d['before'],d['after']);changes.append(d)
 old=L/f'PV_CB_Op118{kind}.lean';assert tok(s)==tok(old.read_text()),kind
 checks.append(dict(kind=kind,raw_sha256=sha(raw.read_bytes()),retained_sha256=sha(old.read_bytes()),retained_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(old.relative_to(R))],text=True).strip(),corrections=changes,tokens_equal=True))
(E/'resume-v218-adapter-check.json').write_text(json.dumps(dict(original_adapter_sha256=sha(p.read_bytes()),checks=checks,generated_output_modified=False,literal_law='PV_RDCD_ShiftLiterals.shift31',authority='h5 existing retained modules; no h7 authority replaced'),indent=2)+'\n');print('Exact historical two-literal adapter relation passes; no generated output modified')
