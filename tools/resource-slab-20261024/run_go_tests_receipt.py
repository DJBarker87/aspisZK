#!/usr/bin/env python3
import hashlib,json,pathlib,resource,subprocess,time
root=pathlib.Path(__file__).resolve().parents[2]
command=['python3','-B','-m','unittest','discover','-s','tools/resource-slab-20261024','-p','test_*.py','-v']
start=time.monotonic()
p=subprocess.run(command,cwd=root,text=True,capture_output=True)
usage=resource.getrusage(resource.RUSAGE_CHILDREN)
evidence=root/'evidence/resource-slab-20261024/go-api'
(evidence/'tests.log').write_text(p.stdout+p.stderr)
(evidence/'tests.json').write_text(json.dumps(dict(command=command,exit=p.returncode,
    wall_seconds=time.monotonic()-start,peak_rss_bytes=usage.ru_maxrss,swaps=usage.ru_nswap,
    platform='macOS; ru_maxrss bytes',source_version=subprocess.check_output(['git','rev-parse','HEAD'],cwd=root,text=True).strip(),
    hashes={str(f.relative_to(root)):hashlib.sha256(f.read_bytes()).hexdigest() for f in sorted((root/'tools/resource-slab-20261024').glob('*.py'))},
    print_axioms='N/A; formal budget ZERO'),indent=2)+'\n')
print(p.stdout+p.stderr)
raise SystemExit(p.returncode)
