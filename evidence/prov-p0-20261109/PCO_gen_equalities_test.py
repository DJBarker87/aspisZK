#!/usr/bin/env python3
"""Offline tests for PCO_gen_equalities.py on the three P0 pilots (no Lean needed).
Gate sources are read from git (git show HEAD:<path>), fresh emissions from the committed PCO_E00n_emitted outputs.
Run: python3 PCO_gen_equalities_test.py   (from this directory)"""
import json, subprocess, sys, tempfile, re, argparse
from pathlib import Path
sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import PCO_gen_equalities as G
def show(path): return subprocess.check_output(['git', 'show', 'HEAD:' + path], cwd=HERE, text=True)
OLD = 'docs/research/100bit-spend-path-20261013/evidence/'
PILOTS = [
 dict(module='AspisR1WideToBytesSource.Funs', run='PCO_E001', ns='PCO_wide_to_bytes', fresh='PCO_wide_to_bytes',
      gate=OLD + 's5-p6-original-serializer-output-20261020/sources/generated-original/Funs.lean', gtypes=OLD + 's5-p6-original-serializer-output-20261020/sources/generated-original/Types.lean',
      expect=dict(common=7, types_identical=4, types_differs=0)),
 dict(module='NFG_CheckedFieldRef.Funs', run='PCO_E002', ns='PCO_checked_field', fresh='PCO_checked_field',
      gate='evidence/slice-q-compose6-20261104/NFG_L018/sources/NFG_CheckedFieldRef/Funs.lean', gtypes='evidence/slice-q-compose6-20261104/NFG_L017/sources/NFG_CheckedFieldRef/Types.lean',
      expect=dict(common=7, types_identical=3, types_differs=0)),
]
def run(p, tmp, state=None, log=None):
    g = tmp / (p['run'] + '_gate.lean'); g.write_text(show(p['gate']))
    gt = tmp / (p['run'] + '_gtypes.lean'); gt.write_text(show(p['gtypes']))
    a = argparse.Namespace(module=p['module'], fresh_dir=str(HERE / (p['run'] + '_emitted/raw/' + p['fresh'])), fresh_ns=p['ns'], gate_source=str(g), gate_types_source=str(gt),
                           partition=str(HERE.parent / 'prov-plan-20261108/PRV_PARTITION.json'), state=state, lean_log=log)
    return G.generate(a)
def main():
    ok = True
    with tempfile.TemporaryDirectory() as t:
        tmp = Path(t)
        for p in PILOTS:
            lean, st, rep = run(p, tmp)
            c = rep['counts']
            checks = [('common', c['common_declarations'] == p['expect']['common']), ('types identical', len(rep['types_identity']['identical']) == p['expect']['types_identical']),
                      ('types differ', len(rep['types_identity']['differs']) == p['expect']['types_differs']), ('no sorry/axiom', not re.search(r'\bsorry\b|^axiom ', lean, re.M)),
                      ('namespace renamed', ('namespace PRVFresh_' + p['module'].replace('.', '_')) in lean and ('namespace ' + p['ns']) not in lean and ('import ' + p['ns']) not in lean),
                      ('probe round', rep['probe_round'] is True), ('every pending theorem has both stages', lean.count('trace "PRV-S1"') == c['common_declarations'] and lean.count('trace "PRV-S2"') == c['common_declarations'])]
            # synthetic probe log: first declaration proved at S1, second fails: expect the second to become a commented obligation
            names = list(st['defs'])
            lines = {n: st['defs'][n]['lines'] for n in names}
            log = tmp / 'fake.log'; fm = 'PRVEq_%s.lean' % p['module'].replace('.', '_')
            rows = []
            for i, n in enumerate(names):
                s, e = lines[n]
                if i == 1: rows.append(f'{fm}:{s}:2: error: synthetic failure')
                else: rows.append(f'{fm}:{s+1}:2: info: PRV-S1')
            log.write_text('\n'.join(rows) + '\n')
            sf = tmp / 'state.json'; sf.write_text(json.dumps(st))
            lean2, st2, rep2 = run(p, tmp, str(sf), str(log))
            checks += [('failure becomes obligation', 'PRV-OBLIGATION' in lean2 and rep2['counts']['failed'] >= 1), ('proved pinned to S1', rep2['counts']['proved_rfl'] == len(names) - 1 or rep2['counts']['failed'] > 1),
                       ('final round has no probe', rep2['probe_round'] is False)]
            for name, v in checks:
                print(('PASS ' if v else 'FAIL ') + p['module'] + ': ' + name); ok &= v
    print('ALL PASS' if ok else 'FAILURES'); sys.exit(0 if ok else 1)
if __name__ == '__main__': main()
