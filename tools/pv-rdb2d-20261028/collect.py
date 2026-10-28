from pathlib import Path
import json,re,hashlib,lzma,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2d-20261028';allowed={'propext','Classical.choice','Quot.sound'};attempts=[]
for n in range(61000,61100):
 p=E/f'lean-{n}/receipt.json';j=json.loads(p.read_text());assert j['attempt']==n and j['swap']=='0'
 if j['exit']==0:
  assert hashlib.sha256((R/j['source_path']).read_bytes()).hexdigest()==j['source_sha256'],n
  for line in j['print_axioms']:
   m=re.search(r'depends on axioms: \[([^]]*)\]',line,re.S)
   if m:assert {x.strip()for x in m[1].split(',')}<=allowed,(n,line)
 j['dependency_fingerprint']='rdb2d-dependency-fingerprint.json.xz';p.write_text(json.dumps(j,indent=2)+'\n')
 attempts.append(dict(attempt=n,module=j['module'],exit=j['exit'],wall=j['wall'],peak_rss_kib=j['peak_rss_kib'],swap=j['swap'],source_revision=j['source_revision'],source_sha256=j['source_sha256'],print_axioms=j['print_axioms'],receipt=str(p.relative_to(E))))
script_map={'rdb2d-preflight':'preflight.py','rdb2d-forest-native':'native-forest.py','rdb2d-collector-binding':'source-forest.py','rdb2d-forest-pairs':'native-pairs.py','rdb2d-sampler-preflight':'sampler-preflight.py','rdb2d-sampler-native':'sampler-native.py','rdb2d-sparse-native':'sparse-native.py','rdb2d-final-fingerprint':'fingerprint.py','rdb2d-cleanup':'cleanup.py'}
head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip();native=[];late=[]
for name,script in script_map.items():
 p=E/name/'receipt.json';j=json.loads(p.read_text());assert j['exit']==0 and j['swap']=='0'
 rel='tools/pv-rdb2d-20261028/'+script;raw=(R/rel).read_bytes();old=subprocess.run(['git','show',j['source_revision']+':'+rel],capture_output=True).stdout
 j['input_script']=dict(path=rel,sha256=hashlib.sha256(raw).hexdigest(),source_revision=head,blob=subprocess.check_output(['git','rev-parse',head+':'+rel],text=True).strip(),present_in_execution_revision=old==raw)
 if old!=raw:late.append(name)
 if name in ['rdb2d-forest-native','rdb2d-forest-pairs','rdb2d-sampler-native','rdb2d-sparse-native']:j['evidence_class']='finite validation only; no universal native source law'
 p.write_text(json.dumps(j,indent=2)+'\n');native.append(dict(name=name,exit=j['exit'],wall=j['wall'],peak_rss_kib=j['peak_rss_kib'],swap=j['swap'],source_revision=j['source_revision'],input_script=j['input_script'],receipt=str(p.relative_to(E))))
raw=lzma.decompress((E/'rdb2d-dependency-fingerprint.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/'rdb2d-dependency-fingerprint.json.sha256').read_text().strip();fp=json.loads(raw)
assert all(x['ok']for x in fp['external']+fp['canonical_ejr']+fp['native_source_checks']);assert not fp['shared_sent_scan']
assert not subprocess.check_output(['git','diff','--name-only','b19cb28c9d','--','crates','programs','design'],text=True).strip()
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RDB2D_*.lean'):
 text=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',text),p;assert not re.search(r'^import .*\bXR',text,re.M),p
assert not [str(p)for p in E.rglob('*')if p.is_file()and p.stat().st_size>20_000_000]
summary=dict(branch='codex/pv-rdb2d-20261028',base='b19cb28c9d',worktree=str(R),restored=[],inherited_restored=['V258','V259'],suspended=['V229','V230','V256','V257','V231','V239'],findings=[],lean_budget=dict(used=100,total=100,success=sum(r['exit']==0 for r in attempts),failure=sum(r['exit']!=0 for r in attempts)),native_budget=dict(used=len(native),total=100),kani=0,attempts=attempts,native_scopes=native,late_native_helper_commits=late,statement_audit=61097,axioms_audit=61098,focused_model_replay=61099,named_theorems_audited=len(json.loads((E/'audit-declarations.json').read_text())['theorems']),allowed_axioms=sorted(allowed),external_objects=len(fp['external']),owned_objects_before_replay=len(fp['objects']),canonical_ejr_objects=len(fp['canonical_ejr']),native_source_checks=fp['native_source_checks'],endpoint_premises=dict(removed=0,added=0,changed=0),T=['entropy_law','entropy_kernel','observation'],composition_trust='reclassification within existing tool trust, never premise removal',stop='100/100 Lean attempts consumed; no complete native source instance restored',next_deliverable='V229 full native collector typed/byte-memory and ownership/destructor refinement retaining full link kind data')
(E/'combined-audit.json').write_text(json.dumps(summary,indent=2)+'\n')
for row in summary['suspended']:
 (E/(row+'.json')).write_text(json.dumps(dict(row=row,disposition='SUSPENDED',class_='B',evidence_class='partial checked models and finite native validation; no restored source-instance credit',exact_blocker_file=row+'.md',statement_audit=61097,axioms_audit=61098,focused_model_replay=61099,endpoint_premises=summary['endpoint_premises'],T=summary['T'],composition_trust=summary['composition_trust']),indent=2)+'\n')
print(json.dumps({k:summary[k]for k in ['lean_budget','native_budget','named_theorems_audited','late_native_helper_commits']}))
