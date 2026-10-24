#!/usr/bin/env python3
"""Instrument unchanged executable source with checked loop invariants only."""
from pathlib import Path
import shutil,hashlib,json
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
parent=H/'aspis-s1-claim-powers-cut-v1-20261024';W=H/'s1-claim-word-partition-v1-20261024'
shutil.copytree(parent,W,ignore=shutil.ignore_patterns('target','.git'))
p=W/'src/lib.rs';original=p.read_text();s=original
shutil.copyfile(H/'s1-word-partition-proofs-20261024.rs',W/'src/proofs.rs')
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
(W/'loop-instrumentation.json').write_text(json.dumps(dict(parent_lib_sha256=hashlib.sha256(original.encode()).hexdigest(),instrumented_lib_sha256=sha(p),proofs_sha256=sha(W/'src/proofs.rs'),executable_token_equality=True,qualification='Original source byte-identical, no loop annotations; common arbitrary normal-return child tapes. No native arithmetic or SDK/effect closure.'),indent=2)+'\n')
print(W)
