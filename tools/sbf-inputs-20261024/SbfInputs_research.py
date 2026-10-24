#!/usr/bin/env python3
"""Official selected Cargo source inspection; no Cargo execution."""
import hashlib,json,pathlib,resource,subprocess,sys,time,urllib.request
start=time.monotonic(); E=pathlib.Path('evidence/sbf-inputs-20261024')
revision='ca74c32f0ac6d99000858dcae9b0931ef76a8f43'; rows=[]
for path in ['src/cargo/sources/registry/mod.rs','src/cargo/sources/registry/local.rs']:
 url=f'https://raw.githubusercontent.com/rust-lang/cargo/{revision}/{path}'
 try:
  with urllib.request.urlopen(url,timeout=30) as f:b=f.read(1000000);status=f.status
  s=b.decode(); lines=s.splitlines(); selected=[]
  for i,line in enumerate(lines):
   if any(k in line for k in ['.cargo-ok','checksum.json','unpack','set_permissions','mtime','cache_path','src_path']):
    selected.append(dict(line=i+1,context='\n'.join(lines[max(0,i-3):i+8])))
  rows.append(dict(url=url,status=status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),selected=selected))
 except Exception as e:rows.append(dict(url=url,error=str(e)))
u=resource.getrusage(0)
out=dict(sources=rows,receipt=dict(command=[sys.executable,'-B',__file__],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swap=u.ru_nswap,print_axioms='N/A'))
with (E/'cargo-extraction-source.json').open('x') as f:json.dump(out,f,indent=2);f.write('\n')
for r in rows:
 print(r['url'],r.get('error',r.get('sha256')))
 for x in r.get('selected',[]): print(x['line'],x['context'])
