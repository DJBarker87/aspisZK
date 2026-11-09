#!/bin/bash
cd "$(dirname "$0")"
R1="--rename-fresh aspis_core.field.M31=field.M31"
R2="--rename-fresh aspis_statement.=  $R1"
gen(){ d=$1; ns=$2; t=$3; shift 3
python3 -B PCUB_gen_equalities.py --partition PCUB_PARTITION.json --module RPu_FIq_NativeTypes --tag=_$t --fresh-dir inputs/fresh_$d --fresh-ns $ns --gate-source inputs/gate/RPu_FIq_NativeTypes.lean --prune-fresh "$@" --out PRVEq_RPu_FIq_NativeTypes_$t.lean --report gen/RPu_FIq_NativeTypes_$t.report1.json --state-out gen/RPu_FIq_NativeTypes_$t.state1.json 2>&1 | tail -3; }
gen T_E037 PCQ_checked_field a
gen T_E039 PCQ_aspis_statement_pool_v1_payment_relation b --rename-fresh aspis_core.field.M31=field.M31
gen T_E040 PCQ_aspis_statement_pool_v1_pair_terminal c --rename-fresh aspis_core.field.M31=field.M31 --rename-fresh aspis_statement.=
gen T_E022 PCQC_adapter_owned_a d --rename-fresh aspis_core.field.M31=field.M31 --rename-fresh aspis_statement.=
gen T_E023 PCQC_adapter_owned_b e --rename-fresh aspis_core.field.M31=field.M31 --rename-fresh aspis_statement.=
