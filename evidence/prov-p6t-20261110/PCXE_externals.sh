#!/bin/bash
# PCXE_externals.sh: splits section c of PCXE_EXTERNALS.json (99 unresolved externals) by crate using PCVG_EXTERNALS_BY_CRATE.json (P3g): 68 aspis-frozen (41 distinct names) stay OPEN_OBLIGATION;
# 16 solana + 15 core/alloc/std name a trust-row proposal (HM-A / HM-D / HM-F) and are counted as DEPENDS_ON_LIBRARY_TRUST (named, not proved). No row is added to any document.
cd /Users/dominic/ZK/.worktrees/pc-prov-p6t/evidence
python3 -I -B - <<'PY'
import json, collections
E = json.load(open('prov-p6t-20261110/PCXE_EXTERNALS.json'))
G = json.load(open('prov-p3g-20261110/PCVG_EXTERNALS_BY_CRATE.json'))
key = lambda gm, n: (gm, n)
g = {key(x['gate_module'], x['name']): x for x in G['entries']}
c = E['c']; miss = []; split = collections.Counter(); named = collections.Counter(); aspis_names = set(); lib_names = collections.defaultdict(set)
for x in c:
    y = g.get(key(x['gate_module'], x['name']))
    if not y: miss.append((x['gate_module'], x['name'])); continue
    x['crate'] = y['crate']; x['trust_row_proposed'] = y['row']; x['class_pcxe'] = 'OPEN_OBLIGATION_ASPIS_FROZEN' if y['crate'] == 'aspis_frozen' else 'DEPENDS_ON_LIBRARY_TRUST_ROW_NAMED'
    split[x['class_pcxe']] += 1
    if y['crate'] == 'aspis_frozen': aspis_names.add(x['name'])
    else: named[y['row']] += 1; lib_names[y['row']].add(x['name'])
assert not miss, miss[:3]
bpf = sorted(n for s in lib_names.values() for n in s if 'bpf_loader_upgradeable' in n)
E['schema'] = 'PCXE_EXTERNALS/2'
E['counts_pcxe'] = dict(a_resolved_by_gate_hand_model_or_constant=len(E['a']), b_covered_by_existing_trust_row=len(E['b']), c_total=len(c), c_aspis_frozen_open_obligation=split['OPEN_OBLIGATION_ASPIS_FROZEN'], c_aspis_frozen_distinct_names=len(aspis_names),
                        c_library_or_sdk_row_named=split['DEPENDS_ON_LIBRARY_TRUST_ROW_NAMED'], c_library_rows=dict(named), c_library_distinct_names={k: len(v) for k, v in lib_names.items()})
E['note_pcxe'] = ('The 68 aspis-frozen externals (41 distinct names) stay open obligations. The 31 library/SDK entries are named by the PCVG_ row proposals (HM-A 16, HM-D 14, HM-F 1) and are counted in the DEPENDS_ON_LIBRARY_TRUST class: named, not proved; the rows are proposals, none is entered in any document. '
                  'solana_sdk_ids bpf_loader_upgradeable.id is not named in the HM-A text of PCXD_TRUST_PROPOSALS.md today: ' + ', '.join(bpf) + ' (entries counted in HM-A by the PCVG_ file).')
json.dump(E, open('prov-p6t-20261110/PCXE_EXTERNALS.json', 'w'), indent=1)
print(E['counts_pcxe'])
PY
