#!/bin/bash
# generate PRVEq_PP_l1.lean : PublicPreparation fresh (e6) vs gate with the carrier map applied to the fresh text
cd "$(dirname "$0")"
python3 -B PCVL_gen_equalities.py --module AspisR1PublicPreparation.Funs --tag "${1:-_l1}" --fresh-dir inputs/fresh_pp --fresh-ns PCVJ_pubprep \
 --gate-source inputs/gate_AspisR1PublicPreparation_Funs.lean --gate-types-source inputs/gatetypes_AspisR1PublicPreparation_Funs.lean \
 --out PRVEq_PP${1:-_l1}.lean --report gen/PP${1:-_l1}.report.json --state-out gen/PP${1:-_l1}.state.json --prune-fresh \
 --rename-fresh aspis_core.digest.Digest32.=aspis_core.Digest32. --rename-fresh aspis_core.digest.Digest32=aspis_core.Digest32 \
 --rename-fresh aspis_core.state_only_prefix.r0.Challenges.=r1_wire.Challenges. --rename-fresh aspis_core.state_only_prefix.r0.Challenges=r1_wire.Challenges \
 --rename-fresh aspis_statement.pool_v1.=pool_v1. \
 --rename-fresh "(Slice (Slice Std.U8))=Slice (Slice Std.U8)" --fresh-prelude inputs/prelude_pp.lean --only inputs/only_pp.json
