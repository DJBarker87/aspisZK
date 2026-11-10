#!/usr/bin/env python3
"""NPS_: copy NPR_R22_CONE.json to NPS_R22_CONE.json with AspisR72Sampler.field.r24_canonical_mul moved
from OPEN to TOTAL_PROVED. NPR_R22_CONE.json is read only. The previous judgment is kept under
nps_judgment_before_r24. Provenance status (NO_FROZEN_COUNTERPART) is NOT changed."""
import json, collections
c = json.load(open('NPR_R22_CONE.json'))
R = 'AspisR72Sampler.field.r24_canonical_mul'
NEW = ("TOTAL_PROVED (a): checked body returns ok on every input of its type "
 "(NPS_, local compiles NPS_C003/NPS_C004: AspisR1.NPS_R24Total.r24_canonical_mul_total, "
 "forall left right, exists out, r24_canonical_mul left right = ok out; per-site lemmas limb_mul_ok, PP_ok, "
 "closure_ok, two_mul_ok, three_P_ok, reduce_ok; the eight >= P guards return ok none). "
 "R22 arithmetic only: provenance remains NO_FROZEN_COUNTERPART (gate-only helper from src/r24_guarded_qm.rs), "
 "a separate source-refinement obligation untouched by this result.")
moved = 0
for e in c['definitions']:
    if e['definition'] == R:
        assert e['nph_judgment'].startswith('OPEN')
        e['nps_judgment_before_r24'] = e['nph_judgment']
        e['nph_judgment'] = NEW
        e['nph_theorems'] = ['AspisR1.NPS_R24Total.r24_canonical_mul_total', 'AspisR1.NPS_R24Total.PP_total',
                             'AspisR1.NPH_R22CM31.R72_r24_closure_total']
        e['nph_open_next_step'] = 'provenance only (NO_FROZEN_COUNTERPART); R22 arithmetic closed'
        e['r22_composition'] = ("checked totality only; wrapping = checked through "
            "R22TotalCheckedComposition.extracted_total_R22 needs the P6 operational interpretation (Translation), "
            "as for the closure call")
        moved += 1
assert moved == 1
def J(e): return (e.get('nph_judgment') or '').split(' ')[0].rstrip(':')
cnt = collections.Counter(); touched = set(); bad = set(); byc = collections.Counter()
for e in c['definitions']:
    if e['body_class'] not in ('CHECKED', 'MIXED'): continue
    j = J(e); cnt[j] += 1; byc[e['body_class'] + '/' + j] += 1
    if j == 'NOT_EXECUTED': continue
    touched |= set(e['rows'])
    if j in ('OPEN', 'DOMAIN_LEMMA_PROVED'): bad |= set(e['rows'])
c['job'] = 'NPS_ 2026-11-10 (copy of NPR_ 2026-11-10 with r24_canonical_mul moved to TOTAL_PROVED)'
c['target_established'] = False
cc = c['counts_checked_and_mixed']
for k in ('TOTAL_PROVED', 'DIRECT', 'DOMAIN_LEMMA_PROVED', 'PRECONDITION_B', 'OPEN', 'NOT_EXECUTED'):
    cc[k] = cnt.get(k, 0)
c['counts_by_class'] = dict(sorted(byc.items()))
c['rows']['with_at_least_one_open_or_domain_only_definition'] = len(bad)
c['rows']['served_only_by_TOTAL_or_DIRECT_definitions'] = len(touched - bad)
c['rows']['touched_by_executed_checked_or_mixed'] = len(touched)
c['revision_note'] = ("updated nps_r24: AspisR72Sampler.field.r24_canonical_mul -> TOTAL_PROVED; counts %d/%d/%d/%d/%d of %d; "
    "rows exposed %d of %d. Previous: " % (cnt['TOTAL_PROVED'], cnt['DIRECT'], cnt['DOMAIN_LEMMA_PROVED'],
    cnt['PRECONDITION_B'], cnt['OPEN'], sum(v for k, v in cnt.items() if k != 'NOT_EXECUTED'), len(bad), len(touched))) + c['revision_note']
json.dump(c, open('NPS_R22_CONE.json', 'w'), indent=1)
print(json.dumps(dict(counts=cnt, touched=len(touched), exposed=len(bad), served=len(touched - bad))))
