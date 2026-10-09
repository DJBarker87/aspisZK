#!/usr/bin/env python3
"""Adapt only the host input adapter; keep all transcript/prover checks."""
from pathlib import Path
import hashlib
import json
here = Path(__file__).resolve().parent
root = here.parents[2]
assert str(root) == "/home/dombarker/project-offloads/aspis-v8-devnet-smoke-20260909"
p = root / "docs/research/v8-no-work-100-20260907/experiments/performance.rs"
s = p.read_text()
before = hashlib.sha256(p.read_bytes()).hexdigest()
old = "let(public,witness,mut snapshot)=we::fixture();"
assert s.count(old) == 1
s = s.replace(old, 'let(public,witness,mut snapshot)=if std::env::var_os("ASPIS_V8_LIVE_CONTEXT").is_some(){live_context::load()}else{we::fixture()};')
old = "let mut runtime=provision_accounts(&witness);"
assert s.count(old) == 1
s = s.replace(old, old + '\n    if std::env::var_os("ASPIS_V8_LIVE_CONTEXT").is_some(){assert_eq!(runtime.anchor_root,public.anchor_root);runtime.pool=public.pool;runtime.deployment_domain=public.deployment_domain;runtime.anchor_sequence=public.anchor_sequence;}')
s = s.replace('use super::*;', 'use super::*;\n#[path="../../v8-isolated-devnet-smoke-20260909/live_context.rs"] mod live_context;')
# Exactly seed 1. No favorable-transcript search or maximum-frontier scan.
s = s.replace('for seed in [1u8,2,3] {', 'assert!(std::env::var_os("ASPIS_V8_MAX_FRONTIER_SCAN").is_none());\n    for seed in [1u8] {')
p.write_text(s)
(here / "prover-input-change.json").write_text(json.dumps({"source":str(p.relative_to(root)),"before_sha256":before,"after_sha256":hashlib.sha256(p.read_bytes()).hexdigest(),"changes":["fixed synthetic note with live deposited membership","live statement runtime binding","one fixed proof seed; no maximum-frontier scan"],"verifier_changed":False},indent=2)+"\n")
