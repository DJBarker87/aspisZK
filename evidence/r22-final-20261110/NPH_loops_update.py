#!/usr/bin/env python3
"""NPH_ item (4) bookkeeping: mechanical body screen for the 30 single-increment bodies and the
NPH_R22_CONE.json update after NPH_L016 (NPH_R22Loops2) and NPH_L017 (NPH_R22Loops3).
Screen: in the census gate body (text before the next doc comment), every monadic binding whose
right side contains a binary arithmetic or shift operator is listed; the body qualifies only if
there is exactly one and it is `<var> + 1#usize`. This is a textual screen, not a proof; the
Lean lemma proves the increment safe under the guard the body states."""
import json,lzma,re,sys
from pathlib import Path
E=Path(__file__).resolve().parent
c=json.loads((E/'NPH_R22_CONE.json').read_text())
B={(b['module'],b['definition']):b for b in json.loads(lzma.decompress((E/'NPH_CENSUS_BODIES.json.xz').read_bytes()))}
L2='AspisR1.NPH_R22Loops2.';L3='AspisR1.NPH_R22Loops3.';G='AspisR1.NPH_R22Loops.usize_succ_ok'
T={ # definition -> (judgment kind, theorem, guard as written in the body)
 'NCX_Reference.zero_loop.body':('T',L2+'ncx_zero_loop_body_total','i < Slice.len b'),
 'NCV_Reference.zero_loop.body':('T',L2+'ncv_zero_loop_body_total','i < Slice.len b'),
 'NCV_Reference.eq_digest_loop.body':('T',L2+'ncv_eq_digest_loop_body_total','i < 8#usize'),
 'NCV_Reference.valid_sequences_loop.body':('T',L2+'ncv_valid_sequences_loop_body_total','i < 8#usize'),
 'NCV_Reference.zero_sequences_loop.body':('T',L2+'ncv_zero_sequences_loop_body_total','i < 8#usize'),
 'NCX_Reference.equal_loop.body':('D',L2+'ncx_equal_loop_body_step','i < Slice.len b'),
 'NCV_Reference.equal_loop.body':('D',L2+'ncv_equal_loop_body_step','i < Slice.len b'),
 'FIq_Native.state_only_poseidon.interpolate_three_constant_columns_loop':('D',L2+'interpolate_three_constant_columns_loop_step','lane < poseidon2.POSEIDON2_WIDTH'),
 'FIq_Native.state_only_poseidon.external_local_packed_raw_loop0':('D',L2+'external_local_packed_raw_loop0_step','output < 4#usize'),
 'FIq_Native.state_only_poseidon.external_local_packed_raw_loop0_loop0':('D',L2+'external_local_packed_raw_loop0_loop0_step','limb < 4#usize'),
 'FIq_Native.state_only_poseidon.external_linear_lazy_loop1':('D',L2+'external_linear_lazy_loop1_step','index < poseidon2.POSEIDON2_WIDTH'),
 'FIq_Native.state_only_poseidon.internal_linear_lazy_loop0':('D',L2+'internal_linear_lazy_loop0_step','lane < poseidon2.POSEIDON2_WIDTH'),
 'FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop0':('D',L2+'pattern_values_literal_loop0_step','limb < poseidon2.POSEIDON2_WIDTH'),
 'FIq_Native.pool_v1.pair_forest_copy_terminal.pattern_values_literal_loop1':('D',L2+'pattern_values_literal_loop1_step','pattern_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_PATTERNS_V1'),
 'FIq_Native.pool_v1.pair_forest_copy_terminal.evaluate_with_selectors_loop':('D',L2+'evaluate_with_selectors_loop_step','link_index < POOL_V1_PAIR_FOREST_COPY_TERMINAL_LINKS_V1'),
 'FIq_Native.pool_v1.pair_forest_copy_terminal.Selectors.active_literal_loop':('D',L2+'active_literal_loop_step','block < 64#usize'),
 'FIq_Native.pool_v1.pair_forest_semantic_terminal.add_value_lanes_loop0':('D',L2+'add_value_lanes_loop0_step','index < 10#usize'),
 'FIq_Native.pool_v1.pair_forest_semantic_terminal.equality_value_loop':('D',L2+'equality_value_loop_step','index < Slice.len (Array.to_slice left)'),
 'FIq_Native.pool_v1.pair_forest_semantic_terminal.semantic_initial_and_absorption':('D',L2+'semantic_initial_rate_succ_ok','none (constant poseidon2.RATE + 1 = 9)'),
 'AspisR1SelectedMaskProbe.array_from_fn_copy_loop':('D',L2+'array_from_fn_copy_loop_step','i < N'),
 'MultiproofSortRef.sort_reference.sort_rows':('D',L2+'sort_rows_step','not (at1 >= n)'),
 'AspisR1Qm31SamplerIndex.sampler.qm31_digits_loop1.body':('D',L3+'qm31_digits_loop1_body_step','i < 4#usize'),
 'AspisR1Post25Sampler.sampler.low_base_p_digits_loop1.body':('D',L3+'low_base_p_digits_loop1_body_step','i < 8#usize'),
 'AspisR1SemanticCallExtraction.r1_semantic.semantic_boundary_loop.body':('D',L3+'semantic_boundary_loop_body_step','index < 28#usize'),
 'S8OwnedP6.finish_owned_loop.body':('D',L3+'finish_owned_loop_body_step','index < Vec.len weights'),
 'AspisR1FinishRelationCurrent.verifier.finish_query_dot_loop.body':('D',L3+'finish_query_dot_loop_body_step','j < Slice.len weights'),
 'AspisS1ValuesOwned.values_owned_reference_loop.body':('D',L3+'values_owned_reference_loop_body_step','chunk < count'),
 'AspisR1CurrentPreparedClaim.verifier.prepared_claim_loop.body':('D',L3+'prepared_claim_loop_body_step','some point from IteratorRange.next (point < iter.end by NHI_RangeProgress.some_next)'),
 'AspisR1CurrentPreparedClaim.verifier.borrowed_abi.owned_claim_loops_loop0.body':('D',L3+'borrowed_abi_owned_claim_loops_loop0_body_step','some point from IteratorRange.next'),
 'AspisR1CurrentPreparedClaim.verifier.owned_claim_loops_loop0.body':('D',L3+'owned_claim_loops_loop0_body_step','some point from IteratorRange.next'),
}
AR=re.compile(r'\s(\+|-|\*|/|%|>>>|<<<)\s')
screen=[];hit=set()
for d in c['definitions']:
 if d['definition'] not in T:continue
 kind,thm,guard=T[d['definition']];hit.add(d['definition'])
 t=B[(d['module'],d['definition'])]['text'].split('\n/--')[0]
 ar=[m.strip() for m in re.findall(r'←\s*([^\n]*)',t) if AR.search(m)]
 ok=len(ar)==1 and re.fullmatch(r'[\w.]+ \+ 1#usize',ar[0]) is not None
 assert ok,(d['definition'],ar)
 assert d['nph_judgment'].startswith('OPEN'),d['definition']
 screen.append(dict(module=d['module'],definition=d['definition'],normalised_body_sha16=d['normalised_body_sha16'],checked_arith_bindings=ar,guard=guard,n_rows=d['n_rows'],theorem=thm))
 d['previous_judgment']=d['nph_judgment']
 if kind=='T':
  d['nph_judgment']='TOTAL_PROVED (a): checked body returns ok on every input (guarded i + 1 via usize_succ_ok; in-bounds index)'
 else:
  d['nph_judgment']=('DIRECT (c): its only overflow-checked operation (body screen NPH_LOOPS_SCREEN.json) is one `+ 1#usize`, '
   'proved safe under the guard the body states ('+guard+'); indexing, update, comparisons and && are not overflow-checks (bounds checks are on in both profiles), '
   'and callees are separate cone definitions with their own R22 judgment, so checked and wrapping executions of the body coincide given agreeing callees')
 d['nph_theorems']=[thm,G];d['open_reason']=None
assert hit==set(T),set(T)-hit
(E/'NPH_LOOPS_SCREEN.json').write_text(json.dumps(dict(schema='NPH_LOOPS_SCREEN/1',kind='textual screen, not a proof',rule=__doc__.strip(),bodies=sorted(screen,key=lambda x:-x['n_rows'])),indent=1)+'\n')
def judg(d):
 j=d['nph_judgment']
 return 'TOTAL_PROVED' if j.startswith('TOTAL') else 'DIRECT' if j.startswith('DIRECT') else 'DOMAIN_LEMMA_PROVED' if j.startswith('DOMAIN') else 'OPEN' if j.startswith('OPEN') else None
from collections import Counter
cm=[d for d in c['definitions'] if d['body_class'] in ('CHECKED','MIXED')];assert len(cm)==225
c['counts_checked_and_mixed']=dict(Counter(judg(d) for d in cm))
c['counts_by_class']=dict(Counter(d['body_class']+'/'+judg(d) for d in cm))
touched=set();exposed=set()
for d in cm:
 touched|=set(d['rows'])
 if judg(d) in ('OPEN','DOMAIN_LEMMA_PROVED'):exposed|=set(d['rows'])
c['rows']=dict(touched_by_checked_or_mixed=len(touched),with_at_least_one_open_or_domain_only_definition=len(exposed),served_only_by_TOTAL_or_DIRECT_definitions=len(touched-exposed))
c['revision_note']='updated after NPH_L017 (NPH_R22Loops2, NPH_R22Loops3): item (4) complete, 5 more TOTAL and 25 more DIRECT single-increment bodies'
(E/'NPH_R22_CONE.json').write_text(json.dumps(c,indent=1,ensure_ascii=False)+'\n')
print(c['counts_checked_and_mixed'],c['counts_by_class'],c['rows'])
