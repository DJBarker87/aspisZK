#!/usr/bin/env python3
"""PCVD item 1: constant-binding modules.  usage: gen_d1.py <module> <out>"""
import sys,json
sys.path.insert(0,'.')
import mkbase,gen_loops,gen_p3
P='pool_v1.pair_forest_semantic_terminal.'
CFG={
 'RPu_FIq_Native09':dict(undrop=[P+'occupancy_lanes_literal'],shims=[('field.QM31.ZERO','field.QM31'),('field.QM31.ONE','field.QM31')]),
 'RPu_FIq_Native11':dict(undrop=[P+'sum_high',P+'poseidon_selectors'],shims=[('field.QM31.ZERO','field.QM31')]),
 'RPu_FIq_Native07':dict(undrop=['state_only_poseidon.interpolate_three_constant_columns',P+'POOL_V1_PAIR_FOREST_SELECTED_TERMINAL_COLUMNS_V1',P+'selected_claim'],shims=[('field.QM31.ZERO','field.QM31'),('state_only_hiding.STATE_ONLY_HIDING_MASK_ONLY_C1_COLUMNS','Std.Usize')]),
 'RPu_FIq_CopyPrefix':dict(undrop=['pool_v1.pair_forest_copy_terminal.link_weight'],
     shims=[('field.M31.ONE','field.M31')]),
 'RPu_FIq_Native05':dict(undrop=['state_only_poseidon.interpolate_three_constant_columns'],
     shims=[('field.QM31.ZERO','field.QM31')]),
 'RPu_FIq_Native10':dict(undrop=[P+'sum_high',P+'initial_variant_selectors',P+'path_lanes_literal'],
     shims=[('field.QM31.ZERO','field.QM31'),('field.QM31.ONE','field.QM31')],
     hoist={P+'path_lanes_literal_loop':{'q':'FIq_Native.field.QM31.ONE'}}),
}
mod,out=sys.argv[1:3]
c=CFG[mod]
mkbase.UNDROP=set(c['undrop'])
mkbase.SHIMS=[f"/-- PCVD constant binding: the cross-crate fresh emission types this constant as `Result`; the gate (and the transparent aspis_core emission) carry the pure value.  Interpretation: `ok <gate constant>`. -/\ndef {n} : Result {t} := ok FIq_Native.{n}" for n,t in c['shims']]
gen_loops.HOIST.update(c.get('hoist',{}))
import re
base_ns=None
# the shim names are qualified once the namespace is known; gen_p3.gen reads the namespace from the base, so patch SHIMNAMES lazily
src=gen_p3.fname(mod)
txt=open(src).read()
ns=re.search(r'namespace (\w+)\nnamespace (PRVFresh_\w+)',txt)
gen_p3.SHIMNAMES[:]=[ns.group(1)+'.'+ns.group(2)+'.'+n for n,t in c['shims']]
print(gen_p3.gen(mod,out,skip=[n for n,t in c["shims"]]))
