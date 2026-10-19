#!/usr/bin/env python3
"""Exact integer envelope preflight; not a Lean proof or Rust-loop refinement."""
import hashlib, json, subprocess
from pathlib import Path
here = Path(__file__).resolve().parent
repo = Path(subprocess.check_output(['git','rev-parse','--show-toplevel'],text=True).strip())
p = 2**31-1
cap = (p-1)**2
pp = p*p
fold_max = p+((2**64-1)//2**31)
partial_max = p+(2*pp)//2**31
checks = {
 'stored_u32_product_fits_u64': (2**32-1)**2 < 2**64,
 'canonical_u32_add_fits': 2*(p-1) < 2**32,
 'canonical_u32_sub_offset_fits': p+(p-1) < 2**32,
 'cm31_cross_product_fits': (2*(p-1))**2 < 2**64,
 'reducer_first_fold_fits': fold_max < 2**64,
 'reducer_second_fold_cast_fits': p+fold_max//2**31 < 2**32,
 'partial_at_most_three_p': partial_max <= 3*p,
 'raw_u_add_fits': cap+pp < 2**64,
 'raw_u_sub_nonnegative': cap <= pp,
 'raw_v_add_fits': 2*cap < 2**64,
 'raw0_ae_pp_fits': cap+pp < 2**64,
 'raw0_bf_sub_nonnegative': cap <= pp,
 'raw0_plus_2u_fits': cap+pp+2*partial_max < 2**64,
 'raw0_plus_3p_fits': cap+pp+2*partial_max+3*p < 2**64,
 'raw0_v_sub_nonnegative': partial_max <= pp-cap+3*p,
 'raw1_sum_fits': 2*cap+3*partial_max < 2**64,
 'raw2_sum_before_sub_fits': 2*cap+2*pp < 2**64,
 'raw2_both_subs_nonnegative': 2*cap <= 2*pp,
 'raw3_all_prefixes_fit': 4*cap < 2**64,
 'batched_retained_plus_four_products': 2**34-1+4*cap < 2**64,
 'fast_dot_seven_folded_batches': 7*(2**34-1) < 2**37,
 'private_dot_4096_folds': 4096*(2**34-1) < 2**46,
 'four_dots_scalar_last_exclusive': 3*120+25*4+4 <= 608,
 'four_dots_last_tail_exclusive': 480+3*32+16+16 == 608,
}
paths = [repo/'crates/aspis-r1-cost-probe/src'/f for f in ['fast_pairing.rs','fast_dots.rs','weights.rs','verifier.rs','r1_semantic.rs','r1_wire.rs']]
r = {'kind':'exact-integer-envelope-preflight','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
 'inputs':[{'path':str(f.relative_to(repo)),'sha256':hashlib.sha256(f.read_bytes()).hexdigest()} for f in paths],
 'constants':{'P':p,'product_cap':cap,'partial_max':partial_max,'u64_max':2**64-1},
 'checks':checks,'exit':0 if all(checks.values()) else 1,
 'limitation':'Exact arithmetic checks only; no emitted-function totality, caller invariant or Lean axiom claim.'}
(here/'bounds-preflight.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps({'checks':len(checks),'exit':r['exit']}))
raise SystemExit(r['exit'])
