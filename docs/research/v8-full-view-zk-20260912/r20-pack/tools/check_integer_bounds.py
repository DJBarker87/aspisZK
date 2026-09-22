#!/usr/bin/env python3
"""Exact integer range certificates for the new word algorithms."""
import json
P=(1<<31)-1;M=P-1;PP=P*P;u64=1<<64
bounds={
 'four_product_max':4*M*M,
 'whole_dot_partial_bound_exclusive':5*P,
 'whole_dot_4096_sum_bound_exclusive':1024*5*P,
 'schoolbook_u_min':PP-M*M,'schoolbook_u_max':PP+M*M,
 'schoolbook_v_max':2*M*M,
 'schoolbook_r0_min':PP-M*M+P-M,
 'schoolbook_r0_max':M*M+PP+3*M+1,
 'schoolbook_i0_max':2*M*M+3*M,
 'schoolbook_r1_min':2*PP-2*M*M,
 'schoolbook_r1_max':2*M*M+2*PP,
 'schoolbook_i1_max':4*M*M,
 'pair_add_lane_max':2*M,'pair_sub_lane_min':P-M,'pair_sub_lane_max':M+P,
}
assert bounds['four_product_max']<u64
assert (bounds['four_product_max']>>31)+P<5*P
assert bounds['whole_dot_4096_sum_bound_exclusive']<(1<<44)
for k,v in bounds.items():
 if k.startswith('schoolbook_'):assert 0<=v<u64,(k,v)
assert bounds['pair_add_lane_max']+1<(1<<32)
assert bounds['pair_sub_lane_max']+1<(1<<32)
print(json.dumps({'bounds':bounds,'all_passed':True,'method':'integer inequalities, not Lean'},indent=2))
