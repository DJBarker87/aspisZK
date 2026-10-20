#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-cu-bound3-20261020
A=$H/analysis
python3 "$H/harness/rebase_rules.py" /home/dombarker/project-offloads/codex-r1-cu-bound2-20261019/artifacts/verifier/linked.elf "$H/artifacts/verifier/linked.elf" "$H/harness/rules-original.json" "$H/harness/rules-rebased.json" "$H/rule-address-mapping.json"
python3 "$H/harness/adopted_rules.py" "$H/harness/rules-rebased.json" "$H/harness/rules.json"
bash "$H/harness/map-analysis.sh" "$A"
python3 "$H/harness/runs_meta.py" "$A/runs.json" "$H/sweep/trace-main/sweep.jsonl" "$H/sweep/trace-control/sweep.jsonl"
python3 "$H/harness/residual.py" "$A" "$A/runs.json" "$H/harness/rules.json" "$A"
python3 "$H/harness/hash_residual.py" "$H" "$A" "$A/hash-residuals.json"
python3 "$H/harness/profile_phases.py" "$H/sweep/profile" "$A/profile-phases.json"
python3 "$H/harness/phase_attrib2.py" "$A" "$A/profile-phases.json" "$A/phase-attribution.json"
python3 "$H/harness/bound2.py" "$A" "$H/harness/rules.json" "$A" "$H/sweep/variants/sweep.jsonl" "$H/sweep/variants-extra/sweep.jsonl" -- "$H/sweep/variants/sweep.jsonl" "$H/sweep/variants-extra/sweep.jsonl" "$H/sweep/targeted/sweep.jsonl" "$H/sweep/random-a/sweep.jsonl" "$H/sweep/random-b/sweep.jsonl" "$H/sweep/control/sweep.jsonl" "$H/sweep/fresh-control/sweep.jsonl"
