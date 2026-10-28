#!/usr/bin/env python3
"""Capture status-only Python validation receipts; no prover launches."""
import argparse
import hashlib
import json
from pathlib import Path
import resource
import subprocess
import sys
import time
E=Path(__file__).resolve().parent
R=E.parent.parent
sha=lambda b:hashlib.sha256(b).hexdigest()
p=argparse.ArgumentParser();p.add_argument('--name',required=True);p.add_argument('--expect-exit',type=int,default=0);p.add_argument('command',nargs=argparse.REMAINDER);a=p.parse_args()
command=a.command[1:] if a.command[:1]==['--'] else a.command
assert command[:1]==['python3'] and command[1].endswith(('_validate.py','_tests.py')), 'only Python audit targets permitted'
start=time.monotonic()
with (E/(a.name+'_RESULT.json')).open('w') as out,(E/(a.name+'_STDERR.log')).open('w') as err:
 result=subprocess.run(command,cwd=R,stdout=out,stderr=err)
u=resource.getrusage(resource.RUSAGE_CHILDREN)
manifest=json.loads((E/'NDK_LEDGER.json').read_text())['evidence_manifest']
receipt=dict(target=command[1],command=command,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),snapshot_revision=json.loads((E/'NDK_SCOPE.json').read_text())['snapshot_revision'],source_tree_dirty=bool(subprocess.check_output(['git','status','--porcelain'],cwd=R)),source_hashes={str(f.relative_to(R)):sha(f.read_bytes()) for f in sorted(E.glob('NDK_*.py'))},ledger_sha256=sha((E/'NDK_LEDGER.json').read_bytes()),associations_sha256=sha((E/'NDK_ASSOCIATIONS.json').read_bytes()),dependency_fingerprint=sha(json.dumps(manifest,sort_keys=True).encode()),exit_status=result.returncode,expected_exit=a.expect_exit,wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss if sys.platform=='darwin' else u.ru_maxrss*1024,swaps=u.ru_nswap,platform=sys.platform,print_axioms='not applicable: Python data validation only; inherited Lean audits pinned, not replayed',cgroup='not applicable: no Lean/Rust/Kani process',lean_attempts=0,kani_attempts=0)
(E/(a.name+'_RECEIPT.json')).write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps({k:receipt[k] for k in ['target','exit_status','expected_exit','wall_seconds','peak_rss_bytes','swaps']}))
sys.exit(0 if result.returncode==a.expect_exit else 1)
