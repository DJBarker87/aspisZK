#!/usr/bin/env python3
from pathlib import Path
import json, os, subprocess
H=Path(__file__).resolve().parent
old=H.parent/'codex-cx-s2e-20261023'
env=dict(os.environ,ASPIS_R18_BEFORE_REVISION='c2d4d0a3c5',ASPIS_R18_AFTER_REVISION='81521c77f7+candidate-sources.json',ASPIS_SOURCE_REVISION='81521c77f7+owned-candidate',ASPIS_R18_BEFORE_BUILD_RECEIPT=str(H/'heap-old-pin.json'),ASPIS_R18_AFTER_BUILD_RECEIPT=str(H/'heap-new-pin.json'))
for name in ['transfer-13','transfer-255','transfer-1023','withdrawal-13','withdrawal-255','withdrawal-1023']:
 f=H/'src/docs/research/100bit-spend-path-20261013/evidence/format-adopt-20261019/fixtures'/name
 cmd=[str(H/'replay-target/release/adapter_rw_replay'),str(H/'heap-artifacts-old/aspis_r1_cost_probe_program.so'),str(H/'heap-artifacts-new/aspis_r1_cost_probe_program.so'),str(f/'r1-s2-proof.bin'),str(f/'r1-s2-public-asf8.bin'),str(H/('heap-replay-'+name))]
 print('fixture',name,flush=True)
 r=subprocess.run(cmd,env=env)
 if r.returncode:raise SystemExit(r.returncode)
