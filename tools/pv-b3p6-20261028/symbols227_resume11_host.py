"""Read-only archive symbol tables; missing inline symbols never prune source bodies."""
from run import H
from pathlib import Path
import subprocess,json,hashlib,lzma
rows=[]
for package in ['aspis_r1_cost_probe','aspis_statement','aspis_core']:
 files=sorted((H/'target/release/deps').glob('lib'+package+'-*.rlib'))
 for p in files:
  r=subprocess.run(['nm','-C','--defined-only',str(p)],text=True,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  text=r.stdout
  q=H/('symbols-resume11-'+p.stem+'.txt.xz')
  with lzma.open(q,'wt')as z:z.write(text)
  rows.append(dict(artifact=str(p),artifact_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),artifact_bytes=p.stat().st_size,command=['nm','-C','--defined-only',str(p)],exit=r.returncode,stdout_sha256=hashlib.sha256(text.encode()).hexdigest(),stdout_bytes=len(text.encode()),stderr=r.stderr,compressed_record=q.name,selected_symbols=[l for l in text.splitlines()if any(n in l for n in ['host_terminal','host_copy_terminal','state_only_poseidon','aspis_core::field'])]))
x=dict(records=rows,missing_packages=[p for p in ['aspis_r1_cost_probe','aspis_statement','aspis_core']if not any(('lib'+p+'-')in r['artifact']for r in rows)],method='read-only release-archive symbols; archive cohort/source-to-shipped-code preservation remains V370; not a source binding, not a call graph, absent symbols never prove dead code')
(H/'symbols-resume11.json').write_text(json.dumps(x,indent=2)+'\n')
print(json.dumps(dict(archives=len(rows),missing=x['missing_packages'])))
