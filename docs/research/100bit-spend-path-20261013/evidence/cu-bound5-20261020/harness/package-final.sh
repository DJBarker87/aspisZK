#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020
A=$H/analysis
python3 "$H/harness/variants_summary.py" "$H/variants-measured.json" "$H/sweep/variants/sweep.jsonl" "$H/sweep/variants-extra/sweep.jsonl" "$H/sweep/targeted/sweep.jsonl" "$H/sweep/random-a/sweep.jsonl" "$H/sweep/random-b/sweep.jsonl" "$H/sweep/control/sweep.jsonl"
python3 "$H/harness/make_deliverables.py" "$A" "$H/harness/rules.json" "$H/variants-measured.json" "$A"
python3 "$H/harness/validate_final.py" "$H"
python3 "$H/harness/inventory.py" "$H"
python3 "$H/harness/source_check.py" "$H"
python3 "$H/harness/cleanup_traces.py" "$H"
python3 "$H/harness/package_check.py" "$H"
