#!/usr/bin/env python3
"""NPR_: copy NPH_R22_CONE.json to NPR_R22_CONE.json with weights.field moved to PRECONDITION_B.
NPH_R22_CONE.json is read only. The previous judgment is kept under npr_judgment_before_wf."""
import json, collections
c = json.load(open('NPH_R22_CONE.json'))
W = 'AspisR1WeightsFieldCurrent.weights.field'
NEW = ("PRECONDITION_B (NPR_, local compiles NPR_C004/C008/C010/C016/C020): the three index operations are ok "
 "for i < 64 (NPH_R22FieldSites.domain_ok) and every executed call site supplies i < 64, proved in Lean. "
 "(1) Finish dot: NPR_R22WeightsWidth.deployed_common_guarded (no premise) shows LIBB_Tx2EnvCode.common runs "
 "its finish only on accumulators whose weights have length 64 (run_finish_congr through the resume Domain, "
 "NNH_Run5bQueryDomain.initial, the op6 query loop as a NPH_R22JoinCW2.Reach state with Domain.width 64 "
 "(query_domain), and Port3_FlushInstall.accepted_contents with raw length 64 from Domain.progress); "
 "NPR_R22DotSite.deployed_common_dot (no premise) adds that the finish dot op4 runs only on slices of length 64 "
 "(finish_op4_congr, op4 = SAG_DotAdapter.sourceDot seed by rfl), and kernel_guarded/dot_guarded show the "
 "dot calls its field slot (= finishField, NPR_Screens.dot_record_field) only at j < 64. "
 "(2) Claim dot: NPR_R22ClaimSite.claim_guarded (owned_claim_loops, the deployed claim body by "
 "NPH_R22JoinCW5.claim_body) calls its field slot only at l < 29; that slot is ClaimParser.field -> finishField "
 "(NPR_Screens.claim_record_field, claimParser_body). "
 "(3) Literal sites: NPR_R22LiteralSites.round_guarded (0 and 4) and poly_guarded (6..0) on the deployed slots "
 "(deployed_round_slots). finishField calls weights.field at its index argument (NPR_Screens.finishField_body). "
 "Remaining textual: that finishField is weights.field's only referrer (NPH_REFS6.json) and the P6/P7 reading.")
moved = 0
for e in c['definitions']:
    if e['definition'] == W:
        e['npr_judgment_before_wf'] = e['nph_judgment']
        e['nph_judgment'] = NEW
        e['nph_pattern_class'] = 'INDEX_ARITHMETIC_ON_CALLER_DOMAIN (sites and producers composed in Lean)'
        e['nph_open_next_step'] = None
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
c['job'] = 'NPR_ 2026-11-10 (copy of NPH_ 2026-11-10 with weights.field moved)'
c['target_established'] = False
cc = c['counts_checked_and_mixed']
for k in ('TOTAL_PROVED', 'DIRECT', 'DOMAIN_LEMMA_PROVED', 'PRECONDITION_B', 'OPEN', 'NOT_EXECUTED'):
    cc[k] = cnt.get(k, 0)
c['counts_by_class'] = dict(sorted(byc.items()))
c['rows']['with_at_least_one_open_or_domain_only_definition'] = len(bad)
c['rows']['served_only_by_TOTAL_or_DIRECT_definitions'] = len(touched - bad)
c['rows']['touched_by_executed_checked_or_mixed'] = len(touched)
json.dump(c, open('NPR_R22_CONE.json', 'w'), indent=1)
print(json.dumps(dict(counts=cnt, touched=len(touched), exposed=len(bad), served=len(touched - bad))))
