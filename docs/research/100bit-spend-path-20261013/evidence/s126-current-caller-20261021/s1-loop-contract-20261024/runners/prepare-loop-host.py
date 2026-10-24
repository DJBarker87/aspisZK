#!/usr/bin/env python3
"""Instrument unchanged executable source with checked loop invariants only."""
from pathlib import Path
import shutil,hashlib,json
H=Path('/home/dombarker/project-offloads/s126-real-sdk-20261021')
parent=H/'aspis-s1-claim-powers-cut-v1-20261024';W=H/'s1-claim-loop-contract-v1-20261024'
shutil.copytree(parent,W,ignore=shutil.ignore_patterns('target','.git'))
p=W/'src/lib.rs';original=p.read_text();s=original
s='#![feature(stmt_expr_attributes, proc_macro_hygiene)]\n'+s
s=s.replace('for point in 0..6 {','#[cfg_attr(kani,kani::loop_invariant(proofs::outer_invariant(kani::index,&parts)))]\n        for point in 0..6 {')
s=s.replace('for l in 0..29 {','#[cfg_attr(kani,kani::loop_invariant(proofs::inner_invariant(point,kani::index,&dot)))]\n            for l in 0..29 {')
s=s.replace('for i in 0..7 {','#[cfg_attr(kani,kani::loop_invariant(proofs::sum_invariant(kani::index,claim)))]\n        for i in 0..7 {')
# Annotations touch only three kinds of loops. Removing exactly the inserted
# attribute lines and feature line recovers executable source modulo indentation.
import re
strip=lambda x:re.sub(r'\s+','',re.sub(r'#\[cfg_attr\(kani,kani::loop_invariant\([^\n]*\)\)\]\n','',x).replace('#![feature(stmt_expr_attributes, proc_macro_hygiene)]\n',''))
assert strip(s)==strip(original)
p.write_text(s);shutil.copyfile(H/'s1-loop-proofs-20261024.rs',W/'src/proofs.rs')
sha=lambda x:hashlib.sha256(x.read_bytes()).hexdigest()
(W/'loop-instrumentation.json').write_text(json.dumps(dict(parent_lib_sha256=hashlib.sha256(original.encode()).hexdigest(),instrumented_lib_sha256=sha(p),proofs_sha256=sha(W/'src/proofs.rs'),executable_token_equality=True,qualification='Verification-only loop invariants; common arbitrary normal-return child tapes. No native arithmetic or SDK/effect closure.'),indent=2)+'\n')
print(W)
