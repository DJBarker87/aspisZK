"""Sequential dependency chunk inside one admitted capped scope; unchanged run2.py."""
import pathlib,json,sys,hashlib,subprocess,time,re,datetime
p=pathlib.Path(sys.argv[1]);a=int(sys.argv[2]);mods=json.loads(sys.argv[3]);plan=json.load(open(p/'build-plan.json'));records=[]
sha=lambda q:hashlib.sha256(q.read_bytes()).hexdigest()
for m in mods:
 rel=m.replace('.','/');s=p/'sources'/(rel+'.lean');o=p/'objects'/(rel+'.olean');o.parent.mkdir(parents=True,exist_ok=True)
 assert not o.exists(), 'never overwrite a completed fresh object: '+m
 pin=plan['modules'][m];assert sha(s)==pin['sha256'],m
 deps={}
 for d in pin['imports']:
  dr=d.replace('.','/')+'.olean';q=next((root/dr for root in [pathlib.Path(q) for q in json.load(open(p/'J.json'))['LEAN_PATH'].split(':')] if (root/dr).is_file()),None)
  assert q is not None,('dependency not fresh or pinned',m,d)
  deps[d]=dict(path=str(q),sha256=sha(q))
 stem=p/'evidence'/f'{a}-{len(records):02d}';out=stem.with_suffix('.out');tim=stem.with_suffix('.time')
 cmd=['/usr/bin/time','-v','-o',str(tim),'timeout','600','python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(p/'J.json'),str(p/'objects'),str(p/'sources'),str(o),str(s),'7000']
 print('START',a,m,flush=True);start=time.monotonic()
 with out.open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
 output=out.read_text();metrics=tim.read_text();get=lambda pattern:re.search(pattern,metrics)
 rss=get(r'Maximum resident set size \(kbytes\): (\d+)');swap=get(r'Swaps: (\d+)');elapsed=get(r'Elapsed \(wall clock\) time \(h:mm:ss or m:ss\): ([0-9:.]+)')
 wall=0
 if elapsed:
  for c in elapsed[1].split(':'):wall=wall*60+float(c)
 rec=dict(module=m,source=pin,source_revision=pin.get('revision',plan['source_revision']),source_sha256=sha(s),dependencies=deps,deps_fingerprint=hashlib.sha256(json.dumps(deps,sort_keys=True).encode()).hexdigest(),exit=r.returncode,wall_seconds=wall,peak_rss_bytes=int(rss[1])*1024 if rss else None,swaps=int(swap[1]) if swap else None,object_sha256=sha(o) if o.is_file() else None,output_path=str(out),output_sha256=sha(out),time_path=str(tim),time_sha256=sha(tim),axioms=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",output),accepted=r.returncode==0 and 'error:' not in output and 'sorryAx' not in output)
 records.append(rec);(p/'evidence'/f'results-{a}.json').write_text(json.dumps(records,indent=2)+'\n')
 print('DONE',a,m,'exit',r.returncode,'wall',wall,'RSS',rec['peak_rss_bytes'],flush=True)
 if not rec['accepted']:
  print(output[-7000:],flush=True);sys.exit(r.returncode or 1)
print('CHUNK COMPLETE',a,len(records),flush=True)
