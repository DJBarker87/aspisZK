#!/usr/bin/env python3
"""Small source-pin gate for D161/F8; not a Rust call-graph proof.

Failing this check means the currently checked-in R1 deployment driver cannot
instantiate the selected proof-account caller. It says nothing against the
documented design or a future, explicitly pinned client.
"""
import hashlib
import json
import re
import resource
import subprocess
import sys
import time
from pathlib import Path

start = time.monotonic()
out = Path(__file__).resolve().parent.parent
root = Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
rows = []
files = subprocess.check_output(['git','ls-files','*.rs'],text=True).splitlines()
for name in files:
    if name.startswith('docs/'):
        continue
    text = (root/name).read_text()
    # All occurrences are retained, including definitions/documentation, so
    # this inventory does not silently count a comment as a production caller.
    for line, value in enumerate(text.splitlines(), 1):
        if re.search(r'\b(generate_for_mask_nonce|prove_masked_retrying_with)\b',value):
            rows.append(dict(path=name,line=line,text=value.strip(),
                             file_sha256=hashlib.sha256(text.encode()).hexdigest()))

driver = 'tools/r1-cost-probe/src/bin/devnet_spend/plan.rs'
text = (root/driver).read_text()
checks = dict(
    selected_retry_call='prover::prove_masked_retrying_with(' in text,
    selected_64byte_factory='StateOnlyAttemptSecrets::generate_for_mask_nonce(' in text,
    actual_96byte_retry_call='prover::prove_masked_retrying(' in text,
)
passed = checks['selected_retry_call'] and checks['selected_64byte_factory']
usage = resource.getrusage(resource.RUSAGE_SELF)
record = dict(source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
              checked_driver=driver,driver_sha256=hashlib.sha256(text.encode()).hexdigest(),checks=checks,
              inventory=rows,exit_status=0 if passed else 1,wall_seconds=time.monotonic()-start,
              peak_rss_kib=usage.ru_maxrss//1024 if sys.platform=='darwin' else usage.ru_maxrss,
              swaps=usage.ru_nswap,print_axioms='N/A: static source check; no compiler launched',
              scope='No production proof-account R1 callback pin identified; profiler and V7 occurrences remain visible.',
              next_deliverable='Pin the actual selected client callback and its nonce policy; certify public-prefix and event producers. No shipped change authorized by this gate.')
(out/'caller-gate.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(dict(exit_status=record['exit_status'],checks=checks,occurrences=len(rows))))
sys.exit(record['exit_status'])
