#!/usr/bin/env python3
"""Collect only bounded own-stage JSON receipts after checking expected pins."""
import hashlib,json,pathlib,resource,shlex,subprocess,time
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-recapture-prep-20261024';start=time.monotonic();rows=[]
a=json.loads((E/'archive.stdout.json').read_text())['raw_manifest'];s=json.loads((E/'source-verify.stdout.json').read_text())['materialized_manifest']
for name,pin in [('archive-members.json',a),('materialized-files.json',s)]:
 assert pin['bytes']<=5000000
 code="import pathlib,sys; p=pathlib.Path('/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024')/"+repr(name)+"; assert p.is_file() and not p.is_symlink(); assert p.stat().st_size<=5000000; sys.stdout.buffer.write(p.read_bytes())"
 cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=15','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)]
 t=time.monotonic();p=subprocess.run(cmd,capture_output=True);assert p.returncode==0,p.stderr
 assert len(p.stdout)==pin['bytes'] and hashlib.sha256(p.stdout).hexdigest()==pin['sha256']
 (E/name).write_bytes(p.stdout);rows.append(dict(command=cmd,exit=p.returncode,wall_seconds=time.monotonic()-t,path=name,sha256=pin['sha256'],bytes=len(p.stdout)))
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
(E/'collect.receipt.json').write_text(json.dumps(dict(command=['python3',str(T/'SbfRecapturePrep_collect.py')],exit=0,results=rows,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),print_axioms='N/A'),indent=2)+'\n')
print('Collected two bounded own-stage manifests with verified digests.')
