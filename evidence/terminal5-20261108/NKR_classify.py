from pathlib import Path
import json,sys,hashlib
E=Path(__file__).resolve().parent
a=sys.argv[1];n=int(a[-3:]);assert a.startswith('NKR_L') and 185<=n<=210
i=n-185
r=json.loads((E/f'NKR_audit/proof{i}/receipt.json').read_text())
g=json.loads((E/'NKR_AUDIT_ROOTS.json').read_text())['groups'][i]
actual=[x['root']for x in r['results']]
assert set(actual)==set(g)and len(actual)==len(g)==len(set(actual))
assert r['standard_only']and all(set(x['walked_axioms'])<={'propext','Quot.sound','Classical.choice'}for x in r['results'])
s=(E/f'NKR_audit/proof{i}/stdout.log').read_text()
diag=[l for l in s.splitlines()if l.strip()and not(l.startswith("'")or l.startswith('NEP_RESULT ') or l.strip() in ['propext,','Classical.choice,','Quot.sound,','propext]','Classical.choice]','Quot.sound]'])]
dis=r['collect_axioms_disagreements']
scope=json.loads((E/a/'receipt.json').read_text());assert scope['exit_status']==r['exit_status']
assert r['exit_status']==0 and not diag or r['exit_status']==1 and dis and diag==['raw graph disagrees with collectAxioms']*len(dis)
row=dict(attempt=a,group=i,original_exit=r['exit_status'],accepted=True,classification='AX2_STANDARD_RAW_COLLECTOR_TOOLING_FINDING'if r['exit_status']else'PASS',root_count=len(actual),disagreements=[dict(root=x['root'],collect_axioms=x['collect_axioms'],walked_axioms=x['walked_axioms'])for x in dis],receipt_sha256=hashlib.sha256((E/f'NKR_audit/proof{i}/receipt.json').read_bytes()).hexdigest(),authority='C3-BIN 2026-11-04 NFO audit treatment: raw walk authoritative; standard omissions are tooling findings. Original process exits and diagnostics retained; no rerun or weakened walker.')
p=E/'NKR_RAW_CLASSIFICATIONS.jsonl'
old=[json.loads(l)for l in p.read_text().splitlines()]if p.exists()else[]
assert not any(x['attempt']==a for x in old),'Classification already retained'
with p.open('a')as f:f.write(json.dumps(row)+'\n')
print(json.dumps({k:row[k]for k in ['attempt','original_exit','classification','root_count']}))
