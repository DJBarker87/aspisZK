"""One small new module, existing cache only. Never invokes a dependency build."""
from pathlib import Path
import os,sys,subprocess,json,hashlib,time,re
root=Path.cwd(); attempt,module=sys.argv[1:]
base=root/'tools/pv-runjoin-20261026/local-proof'
out=root/'evidence/pv-runjoin6-20261026'
source=root/'docs/research/v8-r0-zk-20261009/lean'/(module+'.lean')
paths=[base/'objects',base/'shared-cache',base/'backend-cache']
packages=Path('/Users/dominic/ZK/AspisFormal/.lake/packages')
paths += [p/'.lake/build/lib/lean' for p in packages.iterdir() if (p/'.lake/build/lib/lean').is_dir()]
env=dict(os.environ,LEAN_PATH=':'.join(map(str,paths)))
snap=out/f'{attempt}-{source.stem}.lean.txt';snap.write_bytes(source.read_bytes())
deps={}
for dep in re.findall(r'^import\s+(\S+)',source.read_text(),re.M):
 p=next((p/(dep.replace('.','/')+'.olean') for p in paths if (p/(dep.replace('.','/')+'.olean')).exists()),None)
 assert p, dep
 deps[dep]=dict(path=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size)
cmd=['lake','env','lean','-M7000','--root='+str(root/'docs/research/v8-r0-zk-20261009/lean'),'-o',str(base/'objects'/(module+'.olean')),str(source)]
start=time.perf_counter()
with (out/f'out-{attempt}.log').open('w') as f:
 result=subprocess.run(['/usr/bin/time','-l',*cmd],cwd=base,env=env,stdout=f,stderr=subprocess.STDOUT)
 f.write(f'\nexit={result.returncode}\n')
wall=time.perf_counter()-start;raw=(out/f'out-{attempt}.log').read_text()
rss=re.search(r'^\s*(\d+)\s+maximum resident set size$',raw,re.M)
swaps=re.search(r'^\s*(\d+)\s+swaps$',raw,re.M)
axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",raw)
r=dict(attempt=int(attempt),target=module,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_was_uncommitted=True,source_sha256=hashlib.sha256(snap.read_bytes()).hexdigest(),source_snapshot=snap.name,command=cmd,exit=result.returncode,wall_seconds=wall,peak_rss_bytes=int(rss[1]) if rss else None,swaps=int(swaps[1]) if swaps else None,axioms=axioms,accepted=result.returncode==0 and not any('sorryAx' in s for s in axioms),direct_dependencies_before=deps,resource_policy='authorized small-new-module local exception, Lean -M7000, no dependency build, no host reservation bypass',lean_githash='8c9756b28d64dab099da31a4c09229a9e6a2ef35',mathlib_git='81a5d257c8e410db227a6665ed08f64fea08e997')
(out/f'receipt-{attempt}.json').write_text(json.dumps(r,indent=2)+'\n')
print(raw[-5000:]);print(json.dumps({k:r[k] for k in ['exit','wall_seconds','peak_rss_bytes','swaps','accepted']}))
