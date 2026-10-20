from pathlib import Path
import re, hashlib, json
ROOT = Path(__file__).resolve().parent
SRC = ROOT / 'generated/AspisR1GroupedPairCut'
DST = ROOT / 'adapted/AspisR1GroupedPairCut'
DST.mkdir(parents=True, exist_ok=True)

def strip_resource_options(s):
    s = re.sub(r'(?m)^/\- You can set the .maxHeartbeats. value[^\n]*\nset_option maxHeartbeats [^\n]*\n\n', '', s)
    s = re.sub(r'(?m)^/\- You can set the .maxRecDepth. value[^\n]*\nset_option maxRecDepth [^\n]*\n\n', '', s)
    return s

for name in ['Types', 'Funs']:
    s = strip_resource_options((SRC / f'{name}.lean').read_text())
    if name == 'Funs':
        s = s.replace('import AspisR1GroupedPairCut.FunsExternal\n', '')
        s = s.replace('namespace AspisR1GroupedPairCut\n', '''namespace AspisR1GroupedPairCut

structure weights.WideExactOps where
  add : field.WideExact → field.WideExact → Result field.WideExact
  mul : field.WideExact → field.WideExact → Result field.WideExact
''', 1)
        signatures = [
            'def weights.s2_grouped_inactive_pair_loop0.body\n',
            'def weights.s2_grouped_inactive_pair_loop0\n',
            'def weights.s2_grouped_inactive_pair_loop1_loop0.body\n',
            'def weights.s2_grouped_inactive_pair_loop1_loop0\n',
            'def weights.s2_grouped_inactive_pair_loop1.body\n',
            'def weights.s2_grouped_inactive_pair_loop1\n',
            'def weights.s2_grouped_inactive_pair\n',
        ]
        for sig in signatures:
            if s.count(sig) != 1:
                raise SystemExit(f'expected one signature: {sig!r}')
            s = s.replace(sig, sig + '  (ops : weights.WideExactOps)\n', 1)
        s = s.replace('field.WideExact.add', 'ops.add').replace('field.WideExact.mul', 'ops.mul')
        rewrites = {
            'weights.s2_grouped_inactive_pair_loop0.body\n      coeff': 'weights.s2_grouped_inactive_pair_loop0.body\n      ops coeff',
            'weights.s2_grouped_inactive_pair_loop1_loop0.body\n      group': 'weights.s2_grouped_inactive_pair_loop1_loop0.body\n      ops group',
            'weights.s2_grouped_inactive_pair_loop1_loop0 iter2 group': 'weights.s2_grouped_inactive_pair_loop1_loop0 ops iter2 group',
            'weights.s2_grouped_inactive_pair_loop1.body low': 'weights.s2_grouped_inactive_pair_loop1.body ops low',
            'weights.s2_grouped_inactive_pair_loop0\n      { start': 'weights.s2_grouped_inactive_pair_loop0\n      ops { start',
            'weights.s2_grouped_inactive_pair_loop1\n    { start': 'weights.s2_grouped_inactive_pair_loop1\n    ops { start',
        }
        for old, new in rewrites.items():
            if s.count(old) != 1:
                raise SystemExit(f'expected one call site: {old!r} count={s.count(old)}')
            s = s.replace(old, new, 1)
        if 'FunsExternal' in s or re.search(r'\baxiom\b', s):
            raise SystemExit('external/axiom remains in selected Funs')
    (DST / f'{name}.lean').write_text(s)

report = {
    'raw_types_sha256': hashlib.sha256((SRC / 'Types.lean').read_bytes()).hexdigest(),
    'raw_funs_sha256': hashlib.sha256((SRC / 'Funs.lean').read_bytes()).hexdigest(),
    'adapted_types_sha256': hashlib.sha256((DST / 'Types.lean').read_bytes()).hexdigest(),
    'adapted_funs_sha256': hashlib.sha256((DST / 'Funs.lean').read_bytes()).hexdigest(),
    'adapter': 'remove generated option overrides; remove FunsExternal import; introduce explicit WideExactOps record; thread ops through only the seven generated helper/body definitions and call sites; replace generated add/mul symbols with ops.add/ops.mul; no Rust loop body changes',
}
(ROOT / 'adapter-report.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report))
