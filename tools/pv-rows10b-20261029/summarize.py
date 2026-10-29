from pathlib import Path
import json,hashlib,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rows10b-20261029';base='42760700cbae39587de93f520aed51618e13ef0a'
rows=[]
for p in sorted(E.glob('*/receipt.json')):
 j=json.loads(p.read_text());rows.append(dict(name=p.parent.name,target=j.get('module',j['target']),exit=j['exit'],wall=j['wall'],peak_rss_kib=j['peak_rss_kib'],swap=j['swap'],source_revision=j['source_revision'],source_sha256=j.get('source_sha256'),print_axioms_path=str(p.parent.relative_to(E)/'output.log'),print_axioms=j['print_axioms']))
(E/'attempt-summary.json').write_text(json.dumps(rows,indent=2)+'\n')
s='| Attempt/scope | Exact target | Exit | Wall | Peak RSS KiB | Swap | Source revision | Axioms |\n|---|---|---:|---|---:|---:|---|---|\n'
for j in rows:
 target=j['target'] if isinstance(j['target'],str) else ' '.join(j['target'])
 if not isinstance(j['target'],str):target='native '+j['name']+'; full exact command in receipt.json'
 s+='| '+ ' | '.join([j['name'],target,str(j['exit']),str(j['wall']),str(j['peak_rss_kib']),str(j['swap']),j['source_revision'],f"[full output]({j['print_axioms_path']})"])+' |\n'
(E/'attempt-summary.md').write_text(s)
L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z';sources=sorted(L.glob('PV_ROWS10B_*.lean'));bad=[]
for p in sources:
 s=p.read_text()
 for line in s.splitlines():
  if re.search(r'\b(sorry|admit|native_decide|implemented_by)\b|^\s*axiom\b|^import .*XR',line):bad.append((p.name,line))
assert not bad,bad
paths=subprocess.check_output(['git','diff','--name-only',base],text=True).splitlines()
allowed=lambda p:p.startswith(('evidence/pv-rows10b-20261029/','tools/pv-rows10b-20261029/','docs/research/v8-r0-zk-20261009/lean/R1Z/PV_ROWS10B_'))
assert all(allowed(p)for p in paths),[p for p in paths if not allowed(p)]
large=[str(p.relative_to(R))for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000];assert not large,large
for n in [68697,68698,68699]:
 j=json.loads((E/f'lean-{n}/receipt.json').read_text());assert j['exit']==0
 assert not re.search(r'sorryAx|Lean.ofReduceBool|native_decide',j['print_axioms'])
lean=[j for j in rows if j['name'].startswith('lean-')];native=[j for j in rows if j['name'].startswith('native-')]
v=dict(base=base,lean_attempts=len(lean),lean_pass=sum(j['exit']==0 for j in lean),lean_failed=sum(j['exit']!=0 for j in lean),native_scopes=len(native),native_pass=sum(j['exit']==0 for j in native),kani=0,budget_exhausted=False,rows_restored=0,rows_closed=0,rows_suspended=['V225','V403','V249','V263','V404','V405'],T='unchanged',guard_sha256=hashlib.sha256((R/'tools/pv-rows10b-20261029/lean.py').read_bytes()).hexdigest(),no_forbidden_constructs=True,only_authorized_paths=True,files_over_20MB=large,accepted_theorems=17,audits=[68697,68698,68699],new_source_sha256={p.name:hashlib.sha256(p.read_bytes()).hexdigest()for p in sources},process_deviations='see REPORT.md; block scan late for first failed attempt, private check recovered after combined compile')
(E/'validation.json').write_text(json.dumps(v,indent=2)+'\n');print(json.dumps({k:x for k,x in v.items()if k!='new_source_sha256'}))
(E/'COMMITS.txt').write_text(subprocess.check_output(['git','log','--oneline',base+'..HEAD'],text=True))
