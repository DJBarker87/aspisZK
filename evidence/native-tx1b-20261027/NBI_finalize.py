"""Read-only evidence recovery/source audits, then clean only this job's scratch objects."""
from pathlib import Path
import sys,json,hashlib,subprocess,tarfile,io,re
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import NBI_host as h
R=E.parents[1]
# Freeze audit: every crates/programs regular file, not just selected functions.
ar=subprocess.check_output(['git','archive','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387','crates','programs','Cargo.toml','Cargo.lock'])
expected={}
with tarfile.open(fileobj=io.BytesIO(ar)) as t:
 for m in t:
  if m.isfile():expected[m.name]=hashlib.sha256(t.extractfile(m).read()).hexdigest()
local={n:hashlib.sha256((R/n).read_bytes()).hexdigest() if (R/n).is_file() else None for n in expected}
assert local==expected,'STOP local frozen-source difference'
(E/'NBI_LOCAL_SOURCE_AUDIT.json').write_text(json.dumps(dict(frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',files=expected,all_match=True),indent=2)+'\n')
script=f'''from pathlib import Path
import hashlib,json,os,subprocess,shutil
b=Path({h.B!r});c=Path({h.C!r});cache=Path({h.CACHE!r});s=b/'NBI_src'
expected=json.loads({json.dumps(json.dumps(expected))})
registrations={{'crates/aspis-r1-cost-probe/src/multiproof.rs':'\\n#[cfg(kani)]\\n#[path="NBI_multiproof.rs"]\\nmod NBI_multiproof;\\n','crates/aspis-r1-cost-probe/src/candidate.rs':'\\n#[cfg(kani)]\\n#[path="NBI_keys.rs"]\\nmod NBI_keys;\\n'}}
actual={{}}
for n,wanted in expected.items():
 data=(s/n).read_bytes()
 if n in registrations:
  reg=registrations[n].encode();assert data.endswith(reg);data=data[:-len(reg)]
 actual[n]=hashlib.sha256(data).hexdigest()
assert actual==expected,'STOP scratch frozen source mismatch'
extras=[str(p.relative_to(s)) for root in [s/'crates',s/'programs'] for p in root.rglob('*') if p.is_file() and str(p.relative_to(s)) not in expected]
assert sorted(extras)==['crates/aspis-r1-cost-probe/src/NBI_keys.rs','crates/aspis-r1-cost-probe/src/NBI_multiproof.rs'],extras
pins=lambda paths:{{str(p):dict(sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in paths if p.is_file()}}
cachepins=pins(cache.rglob('*'))
coherent=pins(list(c.glob('*.olean'))+list((c/'objects').rglob('*.olean')))
aeneas=pins([c/'objects/Aeneas.olean']+list((c/'objects/Aeneas').rglob('*.olean')))
tools=[Path('/home/dombarker/.cargo/bin/cargo-kani'),Path('/home/dombarker/.cargo/bin/cargo'),Path('/home/dombarker/.kani/kani-0.67.0/bin/cbmc'),Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler'),Path('/home/dombarker/.kani/kani-0.67.0/bin/kani-driver'),Path('/home/dombarker/.elan/toolchains/leanprover--lean4---v4.32.0/bin/lean'),b/'S2W_run_host.py',b/'S2W_lean_host.py',Path('/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py')]
# No submitted process is restarted. Check terminality before deleting owned objects.
processes=subprocess.check_output(['ps','-eo','pid=,args='],text=True).splitlines()
live=[]
for row in processes:
 pid,_,args=row.strip().partition(' ')
 if int(pid) in [os.getpid(),os.getppid()]:continue
 if {h.B!r} in args and any(x in args for x in ['cargo-kani kani',' kani-compiler ',' cbmc ','S2W_run_host.py NBI_']):live.append(row)
assert not live,live
private_objects=[str(p) for p in b.rglob('*.olean')]
assert not private_objects,private_objects
removed=[]
for name in ['NBI_target','NBI_tmp']:
 p=b/name
 if p.exists():shutil.rmtree(p);removed.append(str(p))
files=list(b.glob('NBI_K*-graph.json'))+list(b.glob('NBI_K*-metadata.stderr'))
recovery={{p.name:p.read_text() for p in files}}
recovery['NBI_TERMINAL_HOST.json']=json.dumps(dict(frozen_sources_equal=True,frozen_file_count=len(expected),harness_extras=extras,live_owned_builds=live,private_objects=private_objects,removed=removed,persistent_cache_retained=str(cache),cache=cachepins,aeneas=aeneas,coherent=coherent,tools=pins(tools)),indent=2)+'\\n'
print(json.dumps(recovery))
'''
r=h.remote_py(script);assert r.returncode==0,r.stderr
for n,s in json.loads(r.stdout).items():(E/n).write_text(s)
initial=json.loads((E/'NBI_INITIAL_HOST_PINS.json').read_text());terminal=json.loads((E/'NBI_TERMINAL_HOST.json').read_text())
assert initial['aeneas']==terminal['aeneas'],'STOP Aeneas object changed'
old=initial['cache'];new=terminal['cache'];changed={k:dict(before=v,after=new.get(k)) for k,v in old.items() if new.get(k)!=v}
(E/'NBI_CACHE_COMPARISON.json').write_text(json.dumps(dict(initial_files=len(old),terminal_files=len(new),changed_initial_files=changed,new_paths=sorted(set(new)-set(old)),aeneas_unchanged=True,persistent_cache_retained=True),indent=2)+'\n')
# Consistent per-attempt ledger; no failed proof or recovery sorryAx is credited.
rows=[]
for p in sorted(E.glob('NBI_*/receipt.json')):
 d=json.loads(p.read_text());row={k:d.get(k) for k in ['attempt','kind','source_revision','source_hashes','command','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms']}
 if d['kind']=='kani':
  g=E/(d['attempt']+'-graph.json');row['kani_launched']=g.exists() and 'kani_exit' in json.loads(g.read_text())
  row['timeout']='CBMC timed out' in (p.parent/'stdout.log').read_text()
 if d['kind']=='lean' and d['exit_status']==0:assert all('sorryAx' not in x for x in d['print_axioms'])
 rows.append(row)
lean=[r for r in rows if r['kind']=='lean'];kani=[r for r in rows if r['kind']=='kani' and r['kani_launched']]
assert len(lean)<=100 and len(kani)<=30
out=dict(lean_attempts=len(lean),lean_passes=sum(r['exit_status']==0 for r in lean),kani_runs=len(kani),kani_passes=sum(r['exit_status']==0 for r in kani),kani_timeouts=sum(r['timeout'] for r in kani),pre_kani_failures=sum(r['kind']=='kani' and not r['kani_launched'] for r in rows),deferred=[],rows=rows)
(E/'NBI_ATTEMPTS.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))
print('Initial cache objects changed:',len(changed))
