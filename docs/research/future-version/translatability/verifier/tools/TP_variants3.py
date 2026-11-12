#!/usr/bin/env python3
"""Aspis translatability pass: third set of variants, around the candidate final tree F (base tree + patch 0 third
version + patches 1 to 3 with canonical_scan in form `unrolled2`). Each variant changes one thing in F.
usage: TP_variants3.py <tree after patch 1> <F tree> <out dir>"""
import subprocess, sys, shutil
from pathlib import Path
U1, F, OUT = [Path(x) for x in sys.argv[1:4]]
HERE = Path(__file__).resolve().parent
C = 'crates/aspis-r1-cost-probe/src/candidate.rs'; A = 'programs/r1-cost-probe/src/r1_pool_adapter.rs'; FU = 'crates/aspis-r1-cost-probe/src/fused.rs'
def emit(name, files, what):
    for f, t in files.items():
        p = OUT / name / f; p.parent.mkdir(parents=True, exist_ok=True); p.write_text(t)
    print(name, '|', what)
for name, form in (('sPinned', 'pinned'), ('sUnr', 'unrolled')):
    tmp = OUT / '.tmp' / name
    subprocess.check_call([sys.executable, '-I', str(HERE / 'TP_rewrite_p2.py'), str(U1), str(tmp), form], stdout=subprocess.DEVNULL)
    emit(name, {C: (tmp / C).read_text()}, 'canonical_scan in form `%s`' % form)
shutil.rmtree(OUT / '.tmp')
t = (F / A).read_text()
old = '''    if (next_leaf_index >> level) & 1 == 0 {
        if node != V7_PAIR_EMPTY_ROOTS[level] {
            Err(ProgramError::InvalidAccountData)
        } else {
            Ok(node)
        }
    } else {
        Ok(node)
    }
'''
assert t.count(old) == 1
emit('lnAlways', {A: t.replace(old, '''    let empty = node == V7_PAIR_EMPTY_ROOTS[level];
    if (next_leaf_index >> level) & 1 == 0 && !empty {
        Err(ProgramError::InvalidAccountData)
    } else {
        Ok(node)
    }
''')}, 'lane frontier helper: the comparison with the empty root made on every level, before the test of the index bit')
t = (F / FU).read_text()
old = '''        let acc: &mut [u64; 416] = match (&mut acc[..]).try_into() {
            Ok(array) => array,
            Err(_) => return Err(Error::Allocation),
        };
'''
assert t.count(old) == 1
emit('btMapErr', {FU: t.replace(old, '''        let acc: &mut [u64; 416] = (&mut acc[..]).try_into().map_err(|_| Error::Allocation)?;
''')}, 'base_lanes_tight with `map_err` and `?` on the mutable array conversion, as before')
for f in (C, A, FU):
    p = OUT / 'B' / f; p.parent.mkdir(parents=True, exist_ok=True); shutil.copyfile(F / f, p)
print('B | the candidate F: copies of 3 files')
