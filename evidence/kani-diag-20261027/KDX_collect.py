from pathlib import Path
import json,sys,hashlib,subprocess,difflib
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));import KDX_host as h
names=[f'KDX_K{i:03}-graph.json' for i in range(1,31)]
r=h.remote_py(f'''from pathlib import Path
import json
b=Path({h.B!r});names={names!r}
print(json.dumps({{n:(b/n).read_text() for n in names}}))''');assert r.returncode==0,r.stderr
for n,t in json.loads(r.stdout).items():(E/n).write_text(t)
ledger=[]
for i in range(1,31):
 a=f'KDX_K{i:03}';d=json.loads((E/a/'receipt.json').read_text());g=json.loads((E/(a+'-graph.json')).read_text());ad=json.loads((E/(a+'-reservation.json')).read_text());t=(E/a/'stdout.log').read_text()
 assert ad['allowed'] is True and g['allowed'] is True and g['unchanged'] is True and g['lock_after']==g['lock_before']
 assert d['limits']=={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
 if 'CBMC timed out' in t:result='TIMEOUT'
 elif 'Checking harness' not in t:result='COMPILE_ERROR'
 elif 'VERIFICATION:- SUCCESSFUL' in t:result='PASS'
 else:result='PROPERTY_FAILURE'
 ledger.append({k:d.get(k) for k in ['attempt','command','source_revision','source_hashes','deps_fingerprint','exit_status','wall_seconds','peak_rss_kib','swaps','print_axioms','cgroup','limits']}|dict(result=result,graph=a+'-graph.json',receipt=a+'/receipt.json'))
(E/'KDX_LEDGER.jsonl').write_text(''.join(json.dumps(x)+'\n' for x in ledger))
# Inspect and hash every frozen release source, plus exact scratch overlays; no build.
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
files=subprocess.check_output(['git','ls-tree','-r','--name-only',frozen,'crates','programs'],text=True).splitlines()
expected={p:subprocess.check_output(['git','rev-parse',frozen+':'+p],text=True).strip() for p in files}
code=f'''from pathlib import Path
import hashlib,json,subprocess
b=Path({h.B!r});s=b/'KDX_src';out=[];patch={{}}
for name,want in {expected!r}.items():
 p=s/name
 if not p.is_file():out.append(dict(path=name,missing=True));continue
 raw=p.read_bytes();actual=hashlib.sha1(b'blob '+str(len(raw)).encode()+b'\\0'+raw).hexdigest()
 if actual!=want:out.append(dict(path=name,frozen_blob=want,actual_blob=actual));patch[name]=raw.decode()
for p in s.rglob('KDX_*.rs'):patch[str(p.relative_to(s))]=p.read_text()
print(json.dumps(dict(source_audit=out,overlays=patch,tools={{n:dict(sha256=hashlib.sha256(Path(p).read_bytes()).hexdigest(),size=Path(p).stat().st_size) for n,p in [('cargo-kani','/home/dombarker/.cargo/bin/cargo-kani'),('cbmc','/home/dombarker/.kani/kani-0.67.0/bin/cbmc'),('kani-compiler','/home/dombarker/.kani/kani-0.67.0/bin/kani-compiler')]}})))'''
# avoid shell argument-length limits
(E/'KDX_collect_host.py').write_text(code);h.admit('KDX_COLLECTUPLOAD')
r=subprocess.run(['scp',str(E/'KDX_collect_host.py'),h.H+':'+h.B+'/KDX_collect_host.py'],capture_output=True,text=True);assert r.returncode==0,r.stderr
r=h.ssh('python3 '+h.B+'/KDX_collect_host.py');assert r.returncode==0,r.stderr
d=json.loads(r.stdout);(E/'KDX_SOURCE_AUDIT.json').write_text(json.dumps({'frozen_revision':frozen,'audited_files':len(expected),'differences':d['source_audit'],'tools':d['tools']},indent=2)+'\n')
allowed={f'crates/aspis-r1-cost-probe/src/{p}.rs' for p in ['multiproof','compact','candidate','verifier','r1_wire']}
assert {x['path'] for x in d['source_audit']}<=allowed
patch=''
for name,t in d['overlays'].items():
 orig=subprocess.check_output(['git','show',frozen+':'+name],text=True,stderr=subprocess.DEVNULL) if name in expected else ''
 if name in allowed:
  # Only appended cfg(kani) imports; native source remains a byte-identical prefix.
  assert t.startswith(orig),name
  suffix=t[len(orig):]
  import re
  assert not re.sub(r'\s*#\[cfg\(kani\)\]\s*#\[path="KDX_\w+\.rs"\]\s*mod KDX_\w+;\s*','',suffix),name
 patch+=''.join(difflib.unified_diff(orig.splitlines(True),t.splitlines(True),fromfile='a/'+name if orig else '/dev/null',tofile='b/'+name))
(E/'KDX_harness.patch').write_text(patch)
print(json.dumps({'runs':len(ledger),'results':{s:sum(x['result']==s for x in ledger) for s in ['PASS','PROPERTY_FAILURE','TIMEOUT','COMPILE_ERROR']},'audited_files':len(expected),'differences':len(d['source_audit'])}))
