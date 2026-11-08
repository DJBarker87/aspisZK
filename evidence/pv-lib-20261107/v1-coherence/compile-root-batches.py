"""Compile array-only root drivers serially inside ONE admitted capped scope."""
import pathlib,json,subprocess,hashlib,re,sys
V=pathlib.Path('/home/dombarker/project-offloads/codex-pv-lib-slice-20261107/v1-coherence');E=V/'evidence';O=V/'objects-canonical';S=V/'sources-canonical';a=int(sys.argv[1]);sha=lambda p:hashlib.file_digest(open(p,'rb'),'sha256').hexdigest();results=[]
for batch in json.load(open(V/'ROOT_BATCHES.json'))['batches']:
 m=batch['name'];s=S/(m+'.lean');o=O/(m+'.olean');assert sha(s)==batch['source_sha256'] and not o.exists();log=E/f'out-{a}-{m}.log';tim=E/f'time-{a}-{m}.log'
 cmd=['/usr/bin/time','-v','-o',str(tim),'python3','/home/dombarker/project-offloads/aspis-fs-generic-20261006/evidence/run2.py',str(V/'J.json'),str(O),str(S),str(o),str(s),'7000']
 with log.open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,cwd=V)
 out=log.read_text();rec=dict(attempt=a,target=m,source_revision=json.load(open(V/'PLAN.json'))['revision'],source_sha256=sha(s),exit=r.returncode,accepted=r.returncode==0,command=cmd,axioms_summary_based=re.findall(r"'[^']+' (?:depends on axioms: \[[\s\S]*?\]|does not depend on any axioms)",out))
 for line in tim.read_text().splitlines():
  for k,f in [('Maximum resident set size (kbytes):','peak_rss_kbytes'),('Swaps:','swaps'),('Elapsed (wall clock) time (h:mm:ss or m:ss):','wall')]:
   if k in line:rec[f]=line.split(k)[1].strip()
 if r.returncode==0:rec['object_sha256']=sha(o)
 (E/f'receipt-{a}-{m}.json').write_text(json.dumps(rec,indent=2));results.append(rec);print(json.dumps({k:rec[k] for k in ['target','exit','wall','peak_rss_kbytes']}),flush=True)
 if r.returncode:print(out);sys.exit(r.returncode)
(E/f'ROOT_BATCH_COMPILES-{a}.json').write_text(json.dumps(results,indent=2))
