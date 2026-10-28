"""Read-only final evidence/source audit; never launches a prover."""
from pathlib import Path
import hashlib,json,re,time,resource,lzma,subprocess
E=Path(__file__).resolve().parent;R=E.parents[1];start=time.monotonic()
def raw(p):return p.read_bytes() if p.exists() else lzma.decompress(Path(str(p)+'.xz').read_bytes())
def sha(p):return hashlib.sha256(raw(p)).hexdigest()
def log(a):
 p=E/a/'stdout.log'
 return p.read_text() if p.exists() else lzma.decompress(p.with_suffix('.log.xz').read_bytes()).decode()
rows=[json.loads(p.read_text()) for p in sorted(E.glob('NCL_[KL][0-9][0-9][0-9]/receipt.json'))]
ledger=[json.loads(s) for s in (E/'NCL_ATTEMPTS.jsonl').read_text().splitlines()]
assert len(rows)==len(ledger) and len({r['attempt'] for r in ledger})==len(rows)
by={r['attempt']:r for r in rows}
for r in rows:
 assert by[r['attempt']]==next(x for x in ledger if x['attempt']==r['attempt'])
 assert r['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64']))
 assert str(r['swaps'])=='0'
 for n,h in r['source_hashes'].items():assert sha(E/r['attempt']/'sources'/n)==h,(r['attempt'],n)
ks=[r for r in rows if r['kind']=='kani'];ls=[r for r in rows if r['kind']=='lean']
assert len(ks)==50 and len(ls)<=80
lock='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef';patch='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
payloads=set()
for r in ks:
 a=r['attempt'];g=json.loads((E/(a+'-graph.json')).read_text())
 assert g['allowed'] and not g['new_packages'] and not g['edge_errors'] and g['unchanged']
 assert g['lock_before']==g['lock_after']==lock
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert r['source_hashes']['NCL_src/Cargo.lock']==lock
 assert r['source_hashes']['NCL_KMX_copy_stubs.patch']==patch
 payloads.add(r['source_hashes']['NCL_src/KMX_stubs.rs'])
assert len(payloads)==1
pairs=[(1,2),(3,4),(5,6),(54,8)]+[(n,n+1) for n in range(9,48,2)]
assert len(pairs)==24
controls=[]
for positive,negative in pairs:
 a=f'NCL_K{positive:03}';b=f'NCL_K{negative:03}'
 assert by[a]['exit_status']==0 and by[b]['exit_status']==1
 assert 'VERIFICATION:- SUCCESSFUL' in log(a)
 text=log(b);assert 'VERIFICATION:- FAILED' in text and 'CBMC timed out' not in text
 if 'Failed Checks:' in text:
  failed=text.split('Failed Checks:',1)[1].split('VERIFICATION:-',1)[0]
  assert 'assertion failed' in failed and 'unwind' not in failed.lower(),b
 else:
  failed='\n'.join(re.findall(r'- Status: FAILURE\n\s*- Description: "([^"]+)"',text))
  assert failed and all('assertion' in s for s in failed.splitlines()),b
 controls.append(dict(positive=a,negative=b,semantic_failure=failed.strip()))
for a in ['NCL_K007','NCL_K051']:assert 'CBMC timed out' in log(a)
allowed={'propext','Classical.choice','Quot.sound'}
roots=[];sources={}
for p in sorted((R/'lean').glob('NCL_*.lean')):
 if p.stem in ['NCL_Audit','NCL_R_Audit']:continue
 text=p.read_text();assert not re.search(r'\b(sorry|admit|native_decide|maxHeartbeats|maxRecDepth)\b',text),p
 assert not re.search(r'^\s*axiom\s',text,re.M)
 ns=re.search(r'^namespace (\S+)',text,re.M).group(1)
 names=re.findall(r'^theorem (\w+)',text,re.M)
 for n in names:
  assert '#print axioms '+n in text,(p,n)
  roots.append(ns+'.'+n)
 h=sha(p);matches=[r for r in ls if r['exit_status']==0 and h in r['source_hashes'].values()]
 assert matches,(p,'no accepted matching source snapshot')
 sources[str(p.relative_to(R))]=dict(sha256=h,accepted_attempt=matches[-1]['attempt'])
for r in ls:
 if r['exit_status']!=0:continue
 for line in r['print_axioms']:
  if 'depends on axioms:' in line:
   atoms=set(line.split('[',1)[1].split(']',1)[0].split(', '));assert atoms<=allowed,line
roots=sorted(set(roots))
latest=by['NCL_L031'];assert latest['exit_status']==0 and len(latest['print_axioms'])==len(roots)
for name in roots:assert any("'"+name+"'" in l for l in latest['print_axioms']),name
frozen=json.loads((E/'NCL_FROZEN_PINS.json').read_text())
for n,h in frozen.items():assert sha(R/n)==h,n
large=[str(p.relative_to(E)) for p in E.rglob('*') if p.is_file() and p.stat().st_size>20_000_000];assert not large,large
recovery=json.loads((E/'NCL_BATCH_RECOVERY.json').read_text())
assert len(recovery['status'])==10 and all(not r['receipt'] and not r['attempt_directory'] and not r['barriers'] for r in recovery['status'])
assert not recovery['observed_live_own_launchers']
out=dict(unresolved_lean_submissions=10,unverified_headline_full_coimport=True,status='PASS_SCOPED_EVIDENCE_PROTOCOL_FINDING_OPEN',unqualified_native_closures=0,lock_topology_finding='NCL_LOCK_COPY_FINDING.md',native_runs=len(ks),native_paired_local_positives=len(pairs),expected_controls=len(controls),excluded_timeouts=['NCL_K007','NCL_K051'],lean_attempts=len(ls),new_theorem_roots=len(roots),latest_audit={k:latest[k] for k in ['attempt','exit_status','wall_seconds','peak_rss_kib','swaps','source_revision','print_axioms']},sources=sources,controls=controls,frozen_source_files=len(frozen),copy_patch_sha256=patch,KMX_payload_sha256=next(iter(payloads)),source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),validation_wall_seconds=time.monotonic()-start,validation_peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,claims='Scoped local native gates and mathematical/model theorems only; enclosing TX1/S2/100-bit target OPEN')
(E/'NCL_VALIDATION.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:out[k] for k in ['status','native_runs','native_paired_local_positives','lean_attempts','new_theorem_roots','frozen_source_files','validation_wall_seconds']}))
