import pathlib, hashlib, subprocess, re, json, sys, time
J=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019')
H=pathlib.Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019')
T=pathlib.Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
D=pathlib.Path('/home/dombarker/project-offloads/codex-cx-wire-len-20261020');D.mkdir(exist_ok=True)
# Usage: remote.py <source-revision> <first-attempt> <module>...
mods=sys.argv[3:]
start=int(sys.argv[2])
assert mods and 6250 <= start and start + len(mods) <= 6300
for a,m in zip(range(start,start+len(mods)),mods):
 src=J/'sources'/(m.replace('.','/')+'.lean')
 imps=re.findall(r'^import (\S+)',src.read_text(),re.M)
 deps=[]
 for imp in sorted(imps):
  obj=J/'objects'/(imp.replace('.','/')+'.olean')
  deps.append({'module':imp,'sha256':hashlib.sha256(obj.read_bytes()).hexdigest() if obj.exists() else 'missing'})
 fp=hashlib.sha256(';'.join(x['module']+'='+x['sha256'] for x in deps).encode()).hexdigest()[:16]
 cmd=['sh',str(H/'tools/run-joint.sh'),str(a),m.replace('.','/'),'J','7000','7',fp]
 p=subprocess.run(cmd,capture_output=True,text=True)
 out=(T/f'out-{a}.log').read_text() if (T/f'out-{a}.log').exists() else p.stdout+p.stderr
 tl=(T/f'time-{a}.log').read_text() if (T/f'time-{a}.log').exists() else ''
 (D/f'out-{a}.log').write_text(out);(D/f'time-{a}.log').write_text(tl)
 def tv(pat):
  mm=re.search(pat,tl);return mm.group(1).strip() if mm else None
 ex=re.search(r'exit=(\d+)',out)
 r={'attempt':a,'module':m,'source_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'deps_fingerprint':fp,'direct_imports':deps,'exit':int(ex[1]) if ex else p.returncode,'wall':tv(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),'peak_rss_kib':int(tv(r'Maximum resident set size \(kbytes\): (\d+)') or 0),'swaps':int(tv(r'Swaps: (\d+)') or 0),'axioms':re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out,re.S),'errors':[x for x in out.splitlines() if 'error:' in x],'command':cmd,'source_revision_parent':sys.argv[1]}
 for dest in [D/'attempts.jsonl',J/'evidence/attempts.jsonl']:
  with dest.open('a') as f:f.write(json.dumps(r)+'\n')
 print(json.dumps(r),flush=True)
 if r['exit'] not in [0,67]:break
