from pathlib import Path
import json,hashlib,subprocess,re,shlex
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-l2d-20261028'
xs=[json.loads((E/f'receipt-{i}.json').read_text()) for i in range(51500,51600)]
assert len(xs)==100 and {r['attempt'] for r in xs}==set(range(51500,51600))
x=json.loads((E/'final-focused-manifest.json').read_text());accepted=x['replay']+x['audits'];names=[]
for row in accepted:
 r=xs[row['attempt']-51500];assert r['exit']==0 and r['source_sha256']==row['source_sha256'];assert all('sorryAx' not in a for a in r['axioms']);names.extend(r['axioms'])
 for a in r['axioms']:
  found=re.search(r'depends on axioms: \[(.*?)\]',a,re.S)
  if found:assert {s.strip() for s in found[1].split(',')} <= {'propext','Quot.sound','Classical.choice'},a
 # Source identity remains frozen through reporting/evidence-only commits.
 assert hashlib.sha256((R/row['source_path']).read_bytes()).hexdigest()==row['source_sha256']
v=dict(lean_compiler_attempts=100,kani_runs=0,focused_attempts=65,final_focused_replay=32,reserved_audits=3,all_final_targets_exit_zero=True,failed_focused_attempts=sum(r['exit']!=0 for r in xs),max_peak_rss_kib=max(r['peak_rss_kib'] for r in xs),total_swaps=sum(r['swaps'] for r in xs),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),standard_axioms_only=True,accepted_final_axioms=names,scope='33 helper modules plus two combined helper audits; no endpoint closure audit',premises_removed=[],retained_rows=json.loads((E/'scope-status.json').read_text())['premises_retained'],target_established=False,stop='100/100 Lean compile budget exhausted; no checked honest leak found')
(E/'FINAL-VALIDATION.json').write_text(json.dumps(v,indent=2)+'\n')
# Read-only collection: do not recompile or modify any shared objects.
mods=[r['module'] for r in accepted]
code='''import pathlib,json,hashlib,sys
p=pathlib.Path('/home/dombarker/project-offloads/codex-pv-l2d-20261028/embedding');out=[]
for m in json.load(sys.stdin):
 s=p/'sources'/(m.replace('.','/')+'.lean');o=p/'objects'/(m.replace('.','/')+'.olean');assert s.is_file() and o.is_file();files=[]
 for x in o.parent.glob(o.stem+'.*'):
  if x.is_file():files.append(dict(path=str(x),sha256=hashlib.sha256(x.read_bytes()).hexdigest()))
 out.append(dict(module=m,source_sha256=hashlib.sha256(s.read_bytes()).hexdigest(),objects=files))
print(json.dumps(out,indent=2))
'''
q=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)],input=json.dumps(mods),text=True,capture_output=True);assert q.returncode==0,q.stderr
(E/'final-private-object-manifest.json').write_text(q.stdout+'\n')
print(json.dumps({k:v[k] for k in ['lean_compiler_attempts','failed_focused_attempts','all_final_targets_exit_zero','max_peak_rss_kib','total_swaps','stop']}))
