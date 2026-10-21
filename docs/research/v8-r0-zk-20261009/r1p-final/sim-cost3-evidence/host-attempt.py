"""One focused env-J attempt; run on the build host with submission JSON."""
import hashlib,json,pathlib,re,subprocess,sys,datetime
j=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019')
t=pathlib.Path('/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence')
h=pathlib.Path('/home/dombarker/project-offloads/r1-privacy-build-integration-20261019')
r=json.load(open(sys.argv[1])); a=r['attempt']; m=r['module']
assert 9560 <= a <= 9599
assert not (t/f'out-{a}.log').exists()
sha=lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert sha(j/'sources'/f'{m}.lean') == r['source_sha256']
deps=[]
for dep, expected in sorted(r['imports'].items()):
 src=j/'sources'/f'{dep}.lean'; obj=j/'objects'/f'{dep}.olean'
 assert sha(src)==expected, f'import changed: {dep}'
 deps.append({'module':dep,'source_sha256':expected,'object_sha256':sha(obj),'object_size':obj.stat().st_size})
r['dependencies']=deps
r['deps_fingerprint']=hashlib.sha256(';'.join(f"{d['module'].replace('/', '.')}={d['object_sha256']}" for d in deps).encode()).hexdigest()[:16]
r['target']=f'{m}.lean (env J retained LEAN_PATH via run-joint.sh/run2.py)'
r['caps']={'lean_memory_mb':7000,'MemoryHigh':'5G','MemoryMax':'7G','MemorySwapMax':0,'TasksMax':128}
r['started_utc']=datetime.datetime.now(datetime.timezone.utc).isoformat()
r['host_preflight']=subprocess.check_output(['sh','-c','date -u; free -k; ps -eo pid,rss,etime,args | rg "bin/lean|aeneas|charon|cargo" || true'],text=True)
p=subprocess.run(['sh',str(h/'tools/run-joint.sh'),str(a),m,'J','7000','7',r['deps_fingerprint']],capture_output=True,text=True)
print(p.stdout,flush=True); print(p.stderr,flush=True)
out=(t/f'out-{a}.log').read_text(); time=(t/f'time-{a}.log').read_text()
def val(pattern):
 mm=re.search(pattern,time); return mm.group(1).strip() if mm else None
r.update(exit=int(re.search(r'^exit=(\d+)$',out,re.M).group(1)),wall=val(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),peak_rss_kib=int(val(r'Maximum resident set size \(kbytes\): (\d+)')),swaps=int(val(r'Swaps: (\d+)')),launcher_stdout=p.stdout,launcher_stderr=p.stderr)
r['axioms']=re.findall(r"^'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out,re.M)
r['errors']=[l for l in out.splitlines() if 'error' in l]
obj=j/'objects'/f'{m}.olean'
if r['exit']==0:r['object']={'sha256':sha(obj),'size':obj.stat().st_size}
# Verify that a concurrent worker did not replace either direct import mid-run.
r['dependencies_stable']=all(sha(j/'objects'/f"{d['module']}.olean")==d['object_sha256'] and sha(j/'sources'/f"{d['module']}.lean")==d['source_sha256'] for d in deps)
pathlib.Path(sys.argv[1]).with_name('attempts.jsonl').write_text(json.dumps(r)+'\n')
sys.exit(r['exit'])
