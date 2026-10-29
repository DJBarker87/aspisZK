#!/usr/bin/env python3
"""Inject one local failure after the buffer-create signing call."""
import pathlib,subprocess,sys
root=pathlib.Path('/home/dombarker/project-offloads/codex-cx-devnet-rehearse-20261029')
claim=root/'evidence/devnet-rehearse-20261029/NDZ_failure-injected'
if claim.exists():
    raise SystemExit('NDZ intentional local signer failure after buffer creation')
claim.touch(exist_ok=False)
raise SystemExit(subprocess.run([str(root/'NDZ_native-target/release/devnet_spend')],input=sys.stdin.buffer.read()).returncode)
