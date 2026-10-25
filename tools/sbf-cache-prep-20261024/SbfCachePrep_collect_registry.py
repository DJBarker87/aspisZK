#!/usr/bin/env python3
"""Collect bounded own manifests by expected digest; no donor reread."""
import hashlib,json,pathlib,resource,shlex,subprocess,time,sys
T=pathlib.Path(__file__).resolve().parent;E=T.parents[1]/'evidence/sbf-cache-prep-20261024';start=time.monotonic();rows=[]
for pin in [json.loads((E/n).read_text())['output'] for n in ['registry.stdout.json','registry-focused.stdout.json']]:
    assert pin['bytes']<=5000000
    path=pathlib.PurePosixPath(pin['path']);assert str(path.parent)=='/home/dombarker/project-offloads/codex-cx-sbf-recapture-20261024/SbfCachePrep-20261024'
    code="import pathlib,resource,sys;resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));p=pathlib.Path("+repr(str(path))+");assert not p.is_symlink() and p.stat().st_size<=5000000;sys.stdout.buffer.write(p.read_bytes())"
    cmd=['ssh','-o','BatchMode=yes','-o','ConnectTimeout=10','dombarker@100.108.41.90','python3 -c '+shlex.quote(code)];t=time.monotonic();p=subprocess.run(cmd,capture_output=True,timeout=60)
    assert p.returncode==0 and len(p.stdout)==pin['bytes'] and hashlib.sha256(p.stdout).hexdigest()==pin['sha256']
    with (E/path.name).open('xb') as f:f.write(p.stdout)
    rows.append(dict(command=cmd,exit=0,wall_seconds=time.monotonic()-t,sha256=pin['sha256'],bytes=len(p.stdout),path=path.name))
u=resource.getrusage(0);c=resource.getrusage(resource.RUSAGE_CHILDREN)
(E/'collect-registry.receipt.json').write_text(json.dumps(dict(command=[sys.executable,'-B',str(pathlib.Path(__file__).resolve())],results=rows,exit=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,children_peak_rss_bytes=c.ru_maxrss,swaps=u.ru_nswap+c.ru_nswap,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),script_sha256=hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),print_axioms='N/A'),indent=2)+'\n');print('Two own manifests collected by exact digest, no donor reread.')
