#!/usr/bin/env python3
"""Seal source-only request/control evidence, no compiler/host execution."""
from pathlib import Path
import argparse,hashlib,json,shutil
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';P=E/'s1-claims-allocator-control-20261025'
a=argparse.ArgumentParser();a.add_argument('--kit',required=True);args=a.parse_args();K=Path(args.kit)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();b=json.loads((K/'binding.json').read_text())
for rel,h in b['files'].items():assert sha(K/rel)==h,rel
P.mkdir(exist_ok=False);shutil.copyfile(K/'binding.json',P/'source-kit-binding.json');files={}
roots=[R/'tools/s1-claims-allocator-control-20261025',P,E/'s1-claims-allocator-preparation-v1']+[E/f's1-claims-allocator-control-v{n}'for n in range(1,5)]
for root in roots:
 for p in root.rglob('*'):
  if p.is_file():
   assert p.suffix not in ['.olean','.ilean','.o','.rlib','.rmeta','.out','.goto','.llbc','.pyc']
   files[str(p.relative_to(R))]=sha(p)
(P/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
 status='COMMON_ALLOCATOR_REQUEST_ERROR_DROP_CONTROL_ONLY',freeze=b['freeze'],candidate_revision=b['candidate_revision'],
 accepted=['s1-claims-allocator-control-v2','s1-claims-allocator-control-v4'],source_only_kit=str(K),files=files,
 print_axioms='N/A: Kani checks, no new Lean theorem or axiom',
 retained=['common null-or-fresh-zeroed allocation cut','no-op deallocation cut','normal-return decoder cut','realloc unreachable check',
 'native allocator/runtime/init/general private-memory/source caller/artifact/adoption joins remain OPEN']),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY_SEALED',files=len(files))))
