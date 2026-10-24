#!/usr/bin/env python3
from pathlib import Path
import shutil,hashlib,json
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021');S=H/'s1-claim-word-partition-v1-20261024';W=H/'s1-claim-word-negative-v1-20261024'
shutil.copytree(S,W,ignore=shutil.ignore_patterns('target','.git'))
shutil.copyfile(H/'s1-word-negative-proofs-20261024.rs',W/'src/proofs.rs')
(W/'negative-control.json').write_text(json.dumps(dict(expected='Verification fails specifically at complete wide-value argument comparison: bit 0 of word 7 is flipped in the expected input only. Original native step and all actual source values unchanged.',parent='s1-claim-word-partition-v1-20261024',proof_sha256=hashlib.sha256((W/'src/proofs.rs').read_bytes()).hexdigest()),indent=2)+'\n')
