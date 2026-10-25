#!/usr/bin/env python3
"""Prepare exact finite unrolled reference; no extraction/SSH execution."""
from pathlib import Path
import json,hashlib,shutil,argparse
R=Path(__file__).resolve().parents[2];T=Path(__file__).resolve().parent
P=Path('/private/tmp/s126-claims-safe-extract-source-release-20261025-v1')
a=argparse.ArgumentParser();a.add_argument('--out',required=True);args=a.parse_args();O=Path(args.out);O.mkdir(mode=0o700,exist_ok=False)
d=json.loads((P/'plan.json').read_text());sha=lambda b:hashlib.sha256(b).hexdigest()
for row in d['source_files']:
 data=(P/row['path']).read_bytes();assert sha(data)==row['sha256'];p=O/row['path'];p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
ref=b'use crate::r1_wire::{Prefix,Error};\nuse alloc::boxed::Box;\nuse aspis_core::field::QM31;\n'+(T/'claims.rs').read_bytes()
p=O/'reference/src/candidate_claims.rs';old_sha=sha(p.read_bytes());p.write_bytes(ref)
for row in d['source_files']:
 if row['path']=='reference/src/candidate_claims.rs':row.update(sha256=sha(ref),kind='Unrolled safe Claims proof reference; native loop/reference Result+allocator/decode/drop-control coupling checked in s1-claims-unrolled-v2')
prep=Path(__file__).read_bytes();(O/'unroll-preparation.py').write_bytes(prep);d['source_files'].append(dict(path='unroll-preparation.py',sha256=sha(prep),kind='Exact source-only unroll materializer'))
d.update(status='PREPARED_UNROLLED_REFERENCE',build_directory='/home/dombarker/project-offloads/s126-real-sdk-20261021/s1-claims-safe-extract-run4-20261025',
 proof_reference=dict(old_candidate_sha256=old_sha,unrolled_source_sha256=sha(ref),loop_count=3,
 kani_target='native_claims::proofs::loop_unrolled',kani_receipt='s1-claims-unrolled-v2/receipt.json',
 qualification='Proof reference only, no frozen source or candidate adoption. Same complete native carriers and original allocation/error/drop interfaces.'))
d['aeneas_command']=[s.replace('AspisS1ClaimsSafeSource','AspisS1ClaimsUnrolledSource')for s in d['aeneas_command']]
(O/'plan.json').write_text(json.dumps(d,indent=2)+'\n')
print('Prepared',len(d['source_files']),'source files; proof reference only')
