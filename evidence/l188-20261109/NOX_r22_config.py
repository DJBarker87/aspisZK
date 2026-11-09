#!/usr/bin/env python3
"""NOX_ T2: classify Stream C gate modules by arithmetic configuration relative to the
deployed (wrapping, overflow-checks off) SBF profile. Input: PCUE_EQ_STATUS.json (P2r).
Rule: a Funs definition PROVED equal to an overflow-checks-ON emission is a checked-semantics
gate body (R22-dependent); a CONFIG_MISMATCH definition is a wrapping gate model (gate uses
wrapping_* where the checked emission is checked); Types definitions carry no arithmetic;
every other status leaves the configuration UNDETERMINED (no overflow-on comparison)."""
import json, collections, sys
from pathlib import Path
here = Path(__file__).resolve().parent
src = here.parent / 'prov-p2r-20261109' / 'PCUE_EQ_STATUS.json'
d = json.loads(src.read_text())
PROVED = {'PROVED_RFL', 'PROVED_UNFOLD', 'PROVED_EQUIV'}
mods = {}
for mod, v in sorted(d['modules'].items()):
    kinds = {p['label']: p['kind'] for p in v.get('passes', [])}
    rec = collections.defaultdict(list)
    for name, r in v.get('reached', {}).items():
        kind = kinds.get(r.get('pass_label'), 'Types' if mod.endswith('Types') else 'Funs')
        st = r['status']
        if st in PROVED and kind != 'Types': rec['checked_funs_proved_equal_to_overflow_on'].append(name)
        elif st in PROVED: rec['types_proved_no_arithmetic'].append(name)
        elif st == 'CONFIG_MISMATCH': rec['wrapping_gate_model_config_mismatch'].append(name)
        else: rec['undetermined_' + st].append(name)
    if rec['checked_funs_proved_equal_to_overflow_on'] and rec['wrapping_gate_model_config_mismatch']: cls = 'MIXED'
    elif rec['checked_funs_proved_equal_to_overflow_on']: cls = 'CHECKED (R22-dependent)'
    elif rec['wrapping_gate_model_config_mismatch']: cls = 'WRAPPING_MODEL'
    elif rec['types_proved_no_arithmetic'] and all(k == 'types_proved_no_arithmetic' or not v2 for k, v2 in rec.items()): cls = 'TYPES_ONLY'
    else: cls = 'UNDETERMINED'
    mods[mod] = {'class': cls, 'counts': {k: len(x) for k, x in rec.items() if x}, 'definitions': {k: sorted(x) for k, x in rec.items() if x}}
summ = collections.Counter(m['class'] for m in mods.values())
out = {'schema': 'NOX_R22_CONFIG/1', 'target_established': False,
       'input': str(src.relative_to(here.parent.parent)), 'deployed_profile': 'release, opt-level=3, no -C overflow-checks, no -C debug-assertions: integer + - * wrap; explicit checked_* still checked; slice indexing and division by zero still abort',
       'rule': __doc__.strip(), 'summary': dict(summ),
       'r22_dependent_modules': sorted(m for m, x in mods.items() if x['class'] in ('CHECKED (R22-dependent)', 'MIXED')),
       'wrapping_model_modules': sorted(m for m, x in mods.items() if x['class'] in ('WRAPPING_MODEL', 'MIXED')),
       'undetermined_modules': sorted(m for m, x in mods.items() if x['class'] == 'UNDETERMINED'),
       'modules': mods}
(here / 'NOX_R22_CONFIG.json').write_text(json.dumps(out, indent=1) + '\n')
print(json.dumps({k: out[k] for k in ('summary', 'r22_dependent_modules', 'wrapping_model_modules')}, indent=1))
