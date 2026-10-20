import datetime,hashlib,json,pathlib,re,subprocess,sys
J=pathlib.Path('/home/dombarker/project-offloads/aspis-joint-20261019'); H=J.parent/'r1-privacy-build-integration-20261019'; T=J.parent/'aspis-fs-generic-20261006'
man=json.loads((J/'evidence/manifest-5-shared-grammar.json').read_text()); mods={e['module']:e for e in man['order']}
m=sys.argv[1]; a=int(sys.argv[2]); assert 6400<=a<=6449
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
src=J/'sources'/(m.replace('.','/')+'.lean'); e=mods[m]; assert sha(src)==e['sha256']
deps=[]
for d in sorted(x for x in e['imports'] if x in mods):
 p=J/'objects'/(d.replace('.','/')+'.olean'); deps.append({'module':d,'sha256':sha(p) if p.exists() else 'missing'})
fp=hashlib.sha256(';'.join(d['module']+'='+d['sha256'] for d in deps).encode()).hexdigest()[:16]
argv=['sh',str(H/'tools/run-joint.sh'),str(a),m.replace('.','/'),'J','7000','7',fp]
p=subprocess.run(argv,capture_output=True,text=True); print(p.stdout,flush=True); print(p.stderr,flush=True)
outpath=T/f'evidence/out-{a}.log'; timepath=T/f'evidence/time-{a}.log'
out=outpath.read_text() if outpath.exists() else p.stdout+p.stderr; tl=timepath.read_text() if timepath.exists() else ''
field=lambda pat:re.search(pat,tl).group(1).strip() if re.search(pat,tl) else None
ex=re.search(r'exit=(\d+)',out)
r={'attempt':a,'module':m,'kind':e['kind'],'repo_source':e['source'],'source_revision':man['repo_revision'],'source_sha256':sha(src),'deps_fingerprint':fp,'imports':deps,'exit':int(ex.group(1)) if ex else p.returncode,'wall':field(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): (.+)'),'peak_rss_kib':int(field(r'Maximum resident set size \(kbytes\): (\d+)') or 0),'swaps':int(field(r'Swaps: (\d+)') or 0),'axioms':[' '.join(s.split()) for s in re.findall(r"'[^']+' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)",out)],'errors':[l for l in out.splitlines() if 'error:' in l],'command':argv,'launcher_exit':p.returncode,'launcher_stdout':p.stdout,'timestamp_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
for path in [J/'evidence/shared-grammar-attempts-6400-6449.jsonl',J/'evidence/attempts.jsonl']:
 with path.open('a') as f: f.write(json.dumps(r)+'\n')
print(json.dumps(r),flush=True)
sys.exit(0 if r['exit'] in (0,67) else r['exit'])
