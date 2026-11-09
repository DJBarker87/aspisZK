#!/bin/bash
# self-copy controls: the gate candidate text (namespace renamed) as the "fresh" emission; require 100% rfl against the compiled gate constants
cd "$(dirname "$0")"
mk(){ # $1 module  $2 tag-less label
  m=$1; d=inputs/fresh_CTL_$m; mkdir -p $d
  perl -pe "s/\\bFIq_Native\\b/CTL_$m/g" inputs/gate/$m.lean > $d/Funs.lean
  perl -pe "s/\\bFIq_Native\\b/CTL_$m/g" inputs/gate/RPu_FIq_NativeTypes.lean > $d/Types.lean
}
for m in RPu_FIq_Native01 RPu_FIq_Native11; do
  mk $m
  python3 -B PCUB_gen_equalities.py --partition PCUB_PARTITION.json --module $m --tag=_ctl --fresh-dir inputs/fresh_CTL_$m --fresh-ns CTL_$m --gate-source inputs/gate/$m.lean --gate-types-source inputs/gate/RPu_FIq_NativeTypes.lean --out PRVEq_${m}_ctl.lean --report gen/${m}_ctl.report1.json --state-out gen/${m}_ctl.state1.json 2>&1 | tail -2
done
# types control
d=inputs/fresh_CTL_RPu_FIq_NativeTypes; mkdir -p $d
perl -pe "s/\\bFIq_Native\\b/CTL_RPu_FIq_NativeTypes/g" inputs/gate/RPu_FIq_NativeTypes.lean > $d/Types.lean
cp $d/Types.lean $d/Funs.lean
python3 -B PCUB_gen_equalities.py --partition PCUB_PARTITION.json --module RPu_FIq_NativeTypes --tag=_ctl --fresh-dir $d --fresh-ns CTL_RPu_FIq_NativeTypes --gate-source inputs/gate/RPu_FIq_NativeTypes.lean --out PRVEq_RPu_FIq_NativeTypes_ctl.lean --report gen/NativeTypes_ctl.report1.json --state-out gen/NativeTypes_ctl.state1.json 2>&1 | tail -2
