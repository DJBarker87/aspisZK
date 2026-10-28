from pathlib import Path
import json,re,hashlib,lzma,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-rdb2c-20261028';config=json.load(open(E/'deployed-native-inputs.json'));attempts=[]
allowed={'propext','Classical.choice','Quot.sound'}
for n in range(60500,60600):
 p=E/f'lean-{n}/receipt.json';j=json.load(open(p));assert j['attempt']==n and j['swap']=='0'
 if j['exit']==0:
  for a in j['print_axioms']:
   m=re.search(r'depends on axioms: \[([^]]*)\]',a,re.S)
   if m:assert set(x.strip() for x in m[1].split(','))<=allowed,(n,a)
  assert hashlib.sha256((R/j['source_path']).read_bytes()).hexdigest()==j['source_sha256'],n
 j['associated_deployed_configuration']='configuration.json';j['dependency_fingerprint']='final-dependency-fingerprint.json.xz';j['rust_compilation_in_this_scope']=False
 if n in [60594,60596]:j['axioms_note']='unchanged canonical EJR generated type/function dependency; data and consuming proof axioms audited at60599'
 p.write_text(json.dumps(j,indent=2)+'\n');attempts.append(dict(attempt=n,module=j['module'],exit=j['exit'],wall=j['wall'],peak_rss_kib=j['peak_rss_kib'],swap=j['swap'],source_revision=j['source_revision'],print_axioms=j['print_axioms'],receipt=str(p.relative_to(E))))
raw=lzma.decompress((E/'final-dependency-fingerprint.json.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/'final-dependency-fingerprint.json.sha256').read_text().strip();fp=json.loads(raw);assert not fp['external_errors']
last=json.load(open(E/'final-replay-object.json'));assert last['source_sha256']==json.load(open(E/'lean-60599/receipt.json'))['source_sha256']
native=[]
for p in sorted(E.glob('*/receipt.json')):
 if p.parent.name.startswith('lean-'):continue
 j=json.load(open(p));assert j['swap']=='0'
 j['associated_deployed_configuration']='configuration.json'
 if p.parent.name in ['native-deployed','deployed-pairs']:
  j.update(resolved_features=config['resolved_features'],profile=config['profile'],toolchain=config['toolchain'],deployed_lock_sha256=config['deployed_lock_sha256'],evidence_class='finite validation and diagnostic source/LLVM binding; no universal native theorem')
 elif p.parent.name in ['native-weights','native-v239','box-llvm-fixed']:
  j['deployed_credit']='EXCLUDED: initial auxiliary dependency drift; replaced by native-deployed/deployed-pairs'
 p.write_text(json.dumps(j,indent=2)+'\n');native.append(dict(name=p.parent.name,exit=j['exit'],wall=j['wall'],peak_rss_kib=j['peak_rss_kib'],swap=j['swap'],source_revision=j['source_revision'],receipt=str(p.relative_to(E))))
status=dict(branch='codex/pv-rdb2c-20261028',base='1a9b7c7f26c9dc0cbce965bcfe2171b7f9dcd763',restored=['V258','V259'],suspended=['V229','V230','V256','V257','V231','V239'],findings=[],lean_budget=dict(used=100,total=100,success=sum(x['exit']==0 for x in attempts),failure=sum(x['exit']!=0 for x in attempts)),native_budget=dict(used=len(native),total=100),kani=0,attempts=attempts,native_scopes=native,statement_axioms_audit=60598,focused_replay=60599,final_axioms_lines=len(attempts[-1]['print_axioms']),allowed_axioms=sorted(allowed),external_objects_verified=len(fp['external_checks']),canonical_ejr_objects=len(fp['canonical_ejr_objects']),owned_objects_pre_replay=len(fp['owned_objects']),final_replay_object=last,endpoint_premises=dict(removed=0,added=0,changed=0),T=['entropy_law','entropy_kernel','observation'],composition_trust='reclassification within existing tool trust; no premise-removal claim',stop='100 Lean attempts spent; six remaining source-instance/world transports need additional proof work',next_deliverable='V229 complete collect/in-place reuse/grow/shrink/deallocation/abort-world trace and public request factorization, then V230 concrete masks callback transport')
(E/'combined-audit.json').write_text(json.dumps(status,indent=2)+'\n')
assert not subprocess.check_output(['git','diff','--name-only','1a9b7c7f26','--','crates','programs'],text=True).strip()
for p in (R/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('PV_RDB2C_*.lean'):
 s=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide|implemented_by|axiom)\b',s),p;assert not re.search(r'^import .*\bXR',s,re.M),p
assert not [p for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000]
print(json.dumps({k:status[k] for k in ['restored','suspended','lean_budget','native_budget','final_axioms_lines']}))
