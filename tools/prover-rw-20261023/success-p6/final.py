"""Read-only continuation audit. Does not run or change proof infrastructure."""
from pathlib import Path
import json,hashlib,subprocess,re
r=Path(__file__).resolve().parents[3];e=r/'docs/research/100bit-spend-path-20261013/evidence/prover-rw-20261023/success-p6'
sha=lambda x:hashlib.sha256(x).hexdigest()
base='e1804622780375b9eb206f2505fa4dc83be5939c'
lean=json.loads((e/'summary.json').read_text())
accepted=[]
for p in (r/'docs/research/v8-r0-zk-20261009/lean/R1Z').glob('ProverRwP6*.lean'):
 matches=[x['attempt'] for x in lean['attempts'] if x['exit']==0 and (e/f"{x['attempt']}.lean.txt").read_bytes()==p.read_bytes()]
 assert matches,p
 accepted.append(dict(path=str(p.relative_to(r)),sha256=sha(p.read_bytes()),attempts=matches))
roots=[]
for name in ['ProverCommitDeployedFuel22','PrivacyR1HeadlineDeployedReal']:
 p=r/f'docs/research/v8-r0-zk-20261009/lean/R1Z/{name}.lean';old=subprocess.check_output(['git','show',base+':'+str(p.relative_to(r))],cwd=r)
 assert old==p.read_bytes();roots.append(dict(path=str(p.relative_to(r)),sha256=sha(old),unchanged=True))
# Retain exact historical reference snapshots by reversing only the recorded edits.
current=(r/'tools/prover-rw-20261023/success-p6/proof/lib.rs').read_text()
owned=current[:current.index('\npub fn wide_bytes_flat')]
original=owned.replace('''        out=write_limb(out,i,limbs[i]); i+=1;''','''        let bytes=limbs[i].to_le_bytes();
        out[4*i]=bytes[0]; out[4*i+1]=bytes[1];
        out[4*i+2]=bytes[2]; out[4*i+3]=bytes[3]; i+=1;''')
original=original.replace('''        let a=aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda);let b=compress(tag,&values,lambda);
        assert_eq!(a.c0.a.0,b.c0.a.0);assert_eq!(a.c0.b.0,b.c0.b.0);assert_eq!(a.c1.a.0,b.c1.a.0);assert_eq!(a.c1.b.0,b.c1.b.0);''','''        assert_eq!(raw(aspis_statement::logup::compress_tagged_tuple(tag,&values,lambda)),raw(compress(tag,&values,lambda)));''')
original=original[:original.index('\npub fn write_limb')]
original=original.replace('''while i<28 { (a,b,c,d)=sum_step(p[i],a,b,c,d); i+=1;}''','''while i<28 {let x=p[i];a+=u64::from(x.c0.a.0);b+=u64::from(x.c0.b.0);c+=u64::from(x.c1.a.0);d+=u64::from(x.c1.b.0);i+=1;}''')
versions=[current,owned,original,subprocess.check_output(['git','show','9b7c45305e:tools/prover-rw-20261023/success-p6/proof/lib.rs'],cwd=r).decode()]
for i,s in enumerate(versions):(e/f'proof-reference-version-{i}.rs.txt').write_text(s)
lookup={sha(s.encode()):f'proof-reference-version-{i}.rs.txt' for i,s in enumerate(versions)}
native=[]
for d in sorted((e/'native').iterdir()):
 if not d.is_dir():continue
 if not (d/'preflight.json').exists():
  x=json.loads((d/'reservation-at-barrier.json').read_text())
  native.append(dict(attempt=d.name,actual_invocations=0,admission_allowed=x['allowed'],bounded_reserved_bytes=x['bounded_reserved_bytes'],safe_limit_bytes=x['safe_limit_bytes'],status='Mandatory stop: non-race reservation denial before target launch'))
  continue
 pre=json.loads((d/'preflight.json').read_text());rec=json.loads((d/'receipt.json').read_text()) if (d/'receipt.json').exists() else None
 raw=(d/'time.log').read_text();m=re.search(r'Exit status: (\d+)',raw)
 command=pre['target'];kani='kani' in command
 ref=pre['source_sha256'].get('tools/prover-rw-20261023/success-p6/proof/lib.rs')
 checks={}
 for path,h in pre['source_sha256'].items():
  if path in ['crates/aspis-core/src/field/wide_exact.rs','crates/aspis-core/src/field.rs','crates/aspis-core/src/state_only_sumcheck.rs','crates/aspis-statement/src/logup.rs','crates/aspis-r1-cost-probe/src/ct_pole.rs']:
   checks[path]=sha((r/path).read_bytes())==h
 assert all(checks.values()),checks
 native.append(dict(attempt=d.name,command=command,kind='Kani' if kani else 'extraction',exit=int(m[1]) if m else None,wall_seconds=rec['wall_seconds'] if rec else None,peak_rss_kib=rec['peak_rss_kib'] if rec else None,swaps=rec['swaps'] if rec else None,limits=pre['limits'],raw_source_revision_label=pre['source_revision'],local_base=base,raw_label_is_not_git_source_pin=True,critical_source_matches_local=checks,proof_reference_sha256=ref,reference_snapshot=lookup.get(ref),receipt_finalization_error=None if rec else 'Missing rustc in invocation PATH; target GNU time and preflight retained; no target rerun unchanged'))
# The three successful native invocations all have exact hash-checked snapshots.
for x in native:
 if x.get('kind')=='Kani' and x.get('exit')==0:assert x['reference_snapshot'],x
result=dict(base_revision=base,accepted_lean_sources=accepted,roots=roots,lean_compiles=lean['lean_compiles'],lean_passes=lean['passes'],lean_budget=70,lean_remaining=70-lean['lean_compiles'],next_env_J=14005,native=native,kani_requests_executed=sum(x.get('kind')=='Kani' for x in native),kani_budget=15,kani_remaining=15-sum(x.get('kind')=='Kani' for x in native),denied_launch_count=sum(x.get('actual_invocations')==0 for x in native),new_source_entries_installed=[],remaining_source_entries=39,root_premises_removed=0,target_established=False,stopped_by='Explicit owner ruling: non-race reservation barrier failure; no retries or infrastructure repairs after denial',pending='Transition current-source interpretation/installation; flat serializer extraction/Kani; boundary scalar-loop extraction; compression compositional Kani; pole full caller',native_passes_scope='Serialization and boundary Result outputs under the pinned native field/constructor methods; no stubs. Pure helpers have no entropy/ROM/TLS effects. No whole execution or artifact adequacy claim.')
(e/'final-state.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['lean_compiles','lean_remaining','kani_requests_executed','kani_remaining','remaining_source_entries','root_premises_removed']},indent=2))
