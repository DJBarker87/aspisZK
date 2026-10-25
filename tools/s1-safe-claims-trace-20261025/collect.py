#!/usr/bin/env python3
"""Seal a source-only paired comparison; does not execute any probe."""
from pathlib import Path
import argparse,hashlib,json,shutil
R=Path(__file__).resolve().parents[2];B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';P=E/'s1-safe-claims-trace-20261025'
a=argparse.ArgumentParser();a.add_argument('--kit',required=True);args=a.parse_args();K=Path(args.kit)
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest();b=json.loads((K/'binding.json').read_text())
for rel,h in b['files'].items():assert sha(K/rel)==h,rel
P.mkdir(exist_ok=False);shutil.copyfile(K/'binding.json',P/'source-kit-binding.json')
files={}
for root in [R/'tools/s1-safe-claims-trace-20261025',P]+[E/f's1-safe-claims-trace-v{n}'for n in range(1,7)]:
 for p in root.rglob('*'):
  if p.is_file():
   assert p.suffix not in ['.olean','.ilean','.o','.rlib','.rmeta','.out','.goto','.llbc','.pyc']
   files[str(p.relative_to(R))]=sha(p)
(P/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
 status='CANDIDATE_NORMAL_RETURN_VALUE_CONTROL_ONLY',freeze=b['freeze'],candidate_revision=b['candidate_revision'],
 positive_characterization='s1-safe-claims-trace-v2',positive_pair='s1-safe-claims-trace-v4',
 excluded_negative='s1-safe-claims-trace-v6',source_only_kit=str(K),files=files,
 qualification='Not TOTAL, initialization, allocator/error/drop/effect/source-runtime-artifact correspondence, source adoption or whole S1/S6 closure.',
 print_axioms='N/A: Kani model checks, no new Lean theorem or axiom'),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY_SEALED',files=len(files))))
