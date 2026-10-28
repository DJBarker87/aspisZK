"""Match fresh outputs to existing committed adapters; never write generated output."""
from pathlib import Path
import re,json,hashlib,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdcd-20261028';L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
def sha(b):return hashlib.sha256(b).hexdigest()
def tokens(s):
 s=s.split('\nnamespace ',1)[1].split('\n',1)[1].rsplit('\nend ',1)[0]
 s=re.sub(r'/\-.*?\-/|--[^\n]*','',s,flags=re.S)
 return re.findall(r'"(?:[^"\\]|\\.)*"|\w+|[^\s]',s)
p=R/'evidence/pv-cb-20261026/op109-normalization.json';adapter=json.loads(p.read_text());assert subprocess.check_output(['git','show','af8459b3e3:'+str(p.relative_to(R))])==p.read_bytes()
results=[]
for row,suffix in [('v213ref','Ref'),('v213bound','')]:
 for kind in ['Types','Funs']:
  raw=E/f'resume-{row}-raw-{kind}.lean.txt';s=raw.read_text();changes=[]
  if kind=='Funs':
   for d in adapter['shift_count_type_adaptations']:
    if d['before'] in s:
     assert s.count(d['before'])==1
     s=s.replace(d['before'],d['after']);changes.append(d)
  retained=L/f'PV_CB_Op109{suffix}{kind}.lean'
  assert tokens(s)==tokens(retained.read_text()),(row,kind)
  results.append(dict(row=row,kind=kind,raw_sha256=sha(raw.read_bytes()),retained_path=str(retained.relative_to(R)),retained_blob=subprocess.check_output(['git','rev-parse','HEAD:'+str(retained.relative_to(R))],text=True).strip(),retained_sha256=sha(retained.read_bytes()),changes=changes,tokens_equal=True))
out=dict(adapter_sha256=sha(p.read_bytes()),results=results,generated_output_modified=False,external_template_imported=False,helper='PV_RDCD_CanonicalSource.reference + exact committed CT source guard; no old Kani credit',literal_laws=['PV_RDCD_ShiftLiterals.shift31','PV_RDCD_ShiftLiterals.shift1'],authority='retained h5 tracked adapter; no h7 authority replacement')
(E/'resume-v213-adapter-check.json').write_text(json.dumps(out,indent=2)+'\n');print('Fresh reference and helper-bound outputs match all four retained modules under exact historical literal adapters')
