#!/bin/bash
# X7: planted controls for the fault scans of gates (iii) and (iv), in the two forms the privacy lead used: the
# planted crate as Charon's own crate (built MIR) and as a dependency of a root crate (optimized MIR, as the Aspis
# library crates are read in the program emissions). One Charon run per form (the program runs' flags: --preset aeneas
# --mir built, nightly-2026-09-17, cargo --release --lib --offline), then the four scans on each LLBC:
# fv_x1b_mutiter.py and fv_x1b_writecalls.py (the name scans), fv_emit_gate_types.py iter and state (the type gates
# iii' and iv'). Also the four scans on the privacy lead's control2 LLBC (ctl2-whole.llbc, crate aspis_rev2b_ctl2,
# from ctl2-out/whole of branch codex/pv-aspis-rev2b-20261112, REVIEW.md section G), as a third form.
# Runs INSIDE one fv_slot.sh scope. Usage: fv_emit_plant.sh <out dir>
set -u
B=$(cd $(dirname $0) && pwd); O=$1; mkdir -p $O
C=/home/dombarker/project-offloads/codex-pc-prov-p4x-20261110/PCWH_T004_out/bin/charon
rm -rf $O/src; cp -r $B/fv_emit_plant $O/src
E="env -u RUSTFLAGS PATH=/home/dombarker/.cargo/bin:/usr/bin:/bin RUSTUP_TOOLCHAIN=nightly-2026-09-17 CARGO_NET_OFFLINE=true CARGO_TARGET_DIR=$O/target"
( cd $O/src/lib && $E $C cargo --preset aeneas --mir built --sysroot default --dest-file $O/crate.llbc -- --release --lib --offline ) > $O/charon-crate.log 2>&1; echo "charon crate form exit $?"
( cd $O/src/root && $E $C cargo --preset aeneas --mir built --sysroot default --start-from crate::root_all --include x7_plant_lib --dest-file $O/dep.llbc -- --release --lib --offline ) > $O/charon-dep.log 2>&1; echo "charon dependency form exit $?"
cp $B/fv_emit_plant/ctl2-whole.llbc $O/ctl2.llbc
for F in crate dep ctl2; do
  PRE=x7_plant; [ $F = ctl2 ] && PRE=aspis_rev2b_ctl2
  [ -f $O/$F.llbc ] || { echo "no $F.llbc"; continue; }
  python3 -I $B/fv_x1b_mutiter.py $O/$F.llbc $PRE > $O/$F-mutiter.tsv 2>&1
  python3 -I $B/fv_emit_gate_types.py iter $O/$F.llbc $PRE > $O/$F-types-iter.tsv 2>&1
  sed 's/startswith(.aspis_.)/startswith(("aspis_","x7_plant","aspis_rev2b"))/' $B/fv_x1b_writecalls.py > $O/writecalls-plant.py
  python3 -I $O/writecalls-plant.py $O/$F.llbc > $O/$F-writecalls.tsv 2>&1
  python3 -I $B/fv_emit_gate_types.py state $O/$F.llbc $PRE > $O/$F-types-state.tsv 2>&1
done
python3 -I - $O <<'PY'
import re, sys
from pathlib import Path
O = Path(sys.argv[1])
own = re.findall(r'pub fn ([is]\d+_\w+)', (O / 'src/lib/src/lib.rs').read_text())
print('function\tform\tfv_x1b_mutiter\tfv_x1b_writecalls\tgate iii (type)\tgate iv (type)\tinformation')
for F in ('crate', 'dep', 'ctl2'):
    def hit(f, pred=lambda l: True):
        p = O / (F + '-' + f + '.tsv')
        if not p.exists(): return set()
        return {l.split('\t')[0].split('::')[-1] for l in p.read_text().splitlines()[1:] if '::' in l.split('\t')[0] and not l.startswith('#') and pred(l)}
    a, c = hit('mutiter'), hit('writecalls')
    b = hit('types-iter', lambda l: '\tFAIL' in l); d = hit('types-state', lambda l: '\tFAIL' in l); e = hit('types-iter', lambda l: '\tINFO' in l)
    fns = own if F != 'ctl2' else re.findall(r'aspis_rev2b_ctl2::(\w+)', (O / 'ctl2-types-iter.tsv').read_text() + (O / 'ctl2-types-state.tsv').read_text() + (O / 'ctl2-mutiter.tsv').read_text()) + ['r_fwd_iter_mut', 'w_rev_split_two_helpers', 'c_refcell_replace', 'c_cell_set', 'w_next_back', 'w_rchunks_mut']
    for fn in sorted(set(fns)):
        if fn in ('i5_helper', 'i6_rev_of'): continue
        y = lambda s: 'fires' if fn in s else '-'
        print('%s\t%s\t%s\t%s\t%s\t%s\t%s' % (fn, F, y(a), y(c), y(b), y(d), 'listed' if fn in e else '-'))
PY
