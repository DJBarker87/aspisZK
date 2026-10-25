#!/usr/bin/env python3
"""Seal source-only native Prepared constructor evidence; performs no build."""
from pathlib import Path
import argparse,hashlib,json,shutil
R=Path(__file__).resolve().parents[2]
B=R/'docs/research/100bit-spend-path-20261013'
E=B/'evidence/s126-current-caller-20261021';P=E/'s1-native-prepared-20261025'
a=argparse.ArgumentParser();a.add_argument('--kit',required=True);args=a.parse_args()
K=Path(args.kit);binding=json.loads((K/'binding.json').read_text())
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
assert not binding['compiler_launched'] and not binding['solver_launched']
for rel,h in binding['files'].items():assert sha(K/rel)==h,rel
P.mkdir(exist_ok=False)
shutil.copyfile(K/'binding.json',P/'source-kit-binding.json')
files={}
roots=[R/'tools/s1-native-prepared-20261025',P]+[E/f's1-native-prepared-v{n}'for n in range(1,7)]
for root in roots:
    for p in root.rglob('*'):
        if p.is_file():
            assert p.suffix not in ['.olean','.ilean','.o','.rlib','.rmeta','.out','.goto','.llbc','.pyc']
            files[str(p.relative_to(R))]=sha(p)
(P/'manifest.json').write_text(json.dumps(dict(schema='focused-extractor-proof-packet-v1',
    status='FOCUSED_NATIVE_CONTROL_ONLY',freeze=binding['freeze'],
    accepted_positive='s1-native-prepared-v6',compile_predecessor='s1-native-prepared-v5',
    superseded_positive='s1-native-prepared-v2 (fixed unobserved metadata and most frame bytes)',
    excluded_negative='s1-native-prepared-v4 (wrong expected scratch address; historical narrower input domain)',
    kit=str(K),kit_is_source_only=True,files=files,
    print_axioms='N/A: Kani result, no new Lean theorem or axiom',
    retained=['six normal-return child cuts','zero-sized test Hash instead of concrete SDK hash',
      'valid S2 View frame lengths and present folded root','canonical private WideExact values',
      'allocation success under default Kani model; no initializedness check',
      'source-context/SDK/native runtime/oracle/release-artifact and enclosing theorem joins']),indent=2)+'\n')
print(json.dumps(dict(status='SOURCE_ONLY_SEALED',files=len(files))))
