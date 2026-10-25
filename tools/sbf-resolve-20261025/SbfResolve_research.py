import hashlib,json,pathlib,subprocess,urllib.request,time
B=pathlib.Path('evidence/sbf-resolve-20261025')
rev='ca74c32f0ac6d99000858dcae9b0931ef76a8f43'
paths=['src/bin/cargo/commands/metadata.rs','src/cargo/ops/cargo_output_metadata.rs','src/cargo/util/rustc.rs','src/cargo/core/compiler/build_context/target_info.rs','src/cargo/ops/resolve.rs']
rows=[]
for p in paths:
 u=f'https://raw.githubusercontent.com/rust-lang/cargo/{rev}/{p}'; t=time.monotonic()
 try:
  with urllib.request.urlopen(u,timeout=25) as f: data=f.read(1000000);status=f.status
  (B/('SbfResolve-source-'+p.replace('/','_')+'.txt')).write_bytes(data)
  rows.append(dict(url=u,status=status,bytes=len(data),sha256=hashlib.sha256(data).hexdigest(),wall_seconds=time.monotonic()-t))
 except Exception as e: rows.append(dict(url=u,error=str(e),wall_seconds=time.monotonic()-t))
(B/'SbfResolve-research.json').write_text(json.dumps(rows,indent=2)+'\n')
for x in rows: print(x)
