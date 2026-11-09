#!/bin/bash
# second chain: extraction specs then the two NDE re-extractions (PCQG_run_nde.py); strictly sequential
export PCQG_HOST_BASE=/home/dombarker/project-offloads/codex-pc-prov-p1f-20261109
cd "$(dirname "$0")"
for x in PCQG_E014:P1F_SEM_A_EO PCQG_E015:P1F_SEM_C_EO PCQG_E016:P1F_ELL; do
  IFS=: read run spec note <<< "$x"
  python3 -B PCQG_render_spec.py "$spec" "$run" "$note" >/dev/null || { echo "$run SPECFAIL" >> PCQG_chain.log; continue; }
  timeout 1500 python3 -B PCQG_run.py "$run" extract > "$run.client.log" 2>&1
  echo "$run $spec rc=$?" >> PCQG_chain.log
done
for x in PCQG_E017:2 PCQG_E018:5; do
  IFS=: read run n <<< "$x"
  python3 -B PCQG_make_nde_specs.py "$run" "$n" >/dev/null
  timeout 1500 python3 -B PCQG_run_nde.py "$run" extract > "$run.client.log" 2>&1
  echo "$run NDE$n rc=$?" >> PCQG_chain.log
done
