#!/bin/bash
# PublicPreparation with transparent aspis_core P/CM31.new/QM31.ZERO (PCVL_E003 emission); carrier map as PCVL_gen_pp.sh; public_bytes and map_err stay callees resolved to the gate
cd "$(dirname "$0")"
python3 -B PCVL_gen_equalities.py --module AspisR1PublicPreparation.Funs --tag "${1:-_l2}" --fresh-dir inputs/fresh_pp3 --fresh-ns PCVL_pp3 \
 --gate-source inputs/gate_AspisR1PublicPreparation_Funs.lean --gate-types-source inputs/gatetypes_AspisR1PublicPreparation_Funs.lean \
 --out PRVEq_PP${1:-_l2}.lean --report gen/PP${1:-_l2}.report.json --state-out gen/PP${1:-_l2}.state.json --prune-fresh \
 --rename-fresh aspis_core.digest.Digest32.=aspis_core.Digest32. --rename-fresh aspis_core.digest.Digest32=aspis_core.Digest32 \
 --rename-fresh aspis_core.state_only_prefix.r0.Challenges.=r1_wire.Challenges. --rename-fresh aspis_core.state_only_prefix.r0.Challenges=r1_wire.Challenges \
 --rename-fresh aspis_statement.pool_v1.=pool_v1. \
 --rename-fresh "(Slice (Slice Std.U8))=Slice (Slice Std.U8)" --only inputs/only_pp3.json
