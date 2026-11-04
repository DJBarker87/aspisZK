#!/usr/bin/env python3
"""Receipt wrapper for Python status checks only; never launches a prover."""
import json
import subprocess
import sys
import time
from pathlib import Path
import NEZ_validate as v

if __name__ == '__main__':
    name = sys.argv[1]
    command = [sys.executable, *sys.argv[2:]]
    start = time.monotonic()
    with (v.E / (name + '.stdout')).open('w') as out, (v.E / (name + '.stderr')).open('w') as err:
        status = subprocess.run(command, cwd=v.R, stdout=out, stderr=err).returncode
    receipt = dict(attempt=name, command=command, target=sys.argv[2:], exit_status=status,
                   wall_seconds=time.monotonic() - start,
                   peak_aggregate_rss_bytes_sampled=v.nen.PEAK_AGGREGATE_RSS,
                   rss_sampling_seconds=0.5, aggregate_rss_stop_bytes=v.nen.CAP,
                   swap='not measured for Python on Darwin; no prover process',
                   source_revision=v.nen.ndt.git('rev-parse', 'HEAD').decode().strip(),
                   source_sha256={str(p.relative_to(v.R)): v.sha(p.read_bytes()) for p in v.E.glob('*.py')},
                   print_axioms='N/A: Python evidence validation; historical audits read only', lean_runs=0, kani_runs=0)
    (v.E / (name + '.json')).write_text(json.dumps(receipt, indent=2) + '\n')
    with (v.E / 'NEZ_ATTEMPTS.jsonl').open('a') as stream:
        stream.write(json.dumps(receipt, sort_keys=True) + '\n')
    print(json.dumps(receipt))
    sys.exit(status)
