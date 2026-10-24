#!/usr/bin/env python3
"""Pin exact official workspace unit identity source without retaining source."""
import hashlib,json,pathlib,resource,subprocess,sys,time,urllib.request
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-cache-prep-20261024';start=time.monotonic();rev='ca74c32f0ac6d99000858dcae9b0931ef76a8f43'
url=f'https://raw.githubusercontent.com/rust-lang/cargo/{rev}/src/cargo/core/compiler/build_runner/compilation_files.rs'
with urllib.request.urlopen(url,timeout=15) as response:b=response.read(2*1024**2+1);status=response.status
assert len(b)<=2*1024**2 and status==200
old=json.loads((E/'cargo-unit-source-initial.json').read_text());assert hashlib.sha256(b).hexdigest()==old['sha256']
u=resource.getrusage(0)
r=dict(url=url,status=status,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b),revision=rev,assessment='Workspace wrapper path enters workspace unit hash at677; version enters artifact identity around792. No GPL source retained.',reason_for_new_receipt='Replace initial inline command rendering with exact retained acquisition script; bytes compared to retained initial receipt.',receipt=dict(command=[sys.executable,'-B',str(pathlib.Path(__file__).resolve())],exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swaps=u.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),print_axioms='N/A'))
(E/'cargo-unit-source.json').write_text(json.dumps(r,indent=2)+'\n')
