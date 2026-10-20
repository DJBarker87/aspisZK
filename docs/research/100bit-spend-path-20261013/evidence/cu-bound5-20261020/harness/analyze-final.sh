#!/bin/bash
set -euo pipefail
H=/home/dombarker/project-offloads/codex-cx-cu-bound5-20261020
A=$H/analysis
O=/home/dombarker/project-offloads/codex-cx-cu-bound4-20261020
python3 "$H/harness/rebase_rules.py" "$O/artifacts/verifier/linked.elf" "$H/artifacts/verifier/linked.elf" "$O/harness/rules.json" "$H/harness/rules-rebased.json" "$H/rule-address-mapping.json"
python3 "$H/harness/candidate_rules.py" "$H" "$A" "$H/harness/rules-rebased.json" "$H/harness/rules.json"
python3 "$H/harness/residual.py" "$A" "$A/runs.json" "$H/harness/rules.json" "$A"
python3 "$H/harness/hash_residual.py" "$H" "$A" "$A/hash-residuals.json"
python3 "$H/harness/profile_phases.py" "$H/sweep/profile" "$A/profile-phases.json"
python3 "$H/harness/phase_attrib2.py" "$A" "$A/profile-phases.json" "$A/phase-attribution.json"
python3 "$H/harness/bound2.py" "$A" "$H/harness/rules.json" "$A" "$H/sweep/variants/sweep.jsonl" "$H/sweep/variants-extra/sweep.jsonl" -- "$H/sweep/variants/sweep.jsonl" "$H/sweep/variants-extra/sweep.jsonl" "$H/sweep/targeted/sweep.jsonl" "$H/sweep/random-a/sweep.jsonl" "$H/sweep/random-b/sweep.jsonl" "$H/sweep/control/sweep.jsonl"
python3 "$H/harness/variants_summary.py" "$H/variants-measured.json" "$H/sweep/variants/sweep.jsonl" "$H/sweep/variants-extra/sweep.jsonl"
python3 "$H/harness/make_deliverables.py" "$A" "$H/harness/rules.json" "$H/variants-measured.json" "$A"
python3 "$H/harness/validate_final.py" "$H"
