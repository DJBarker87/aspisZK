"""Restore the original empty modifies clause as well as each value predicate."""
from NEK_box_context import *
for aidx,num in zip(range(198,204),range(32,38)):
 a=f'NEK_K{aidx:03}';rp=f'evidence/slice-s-leaves-20261029/NEC_K{num:03}/receipt.json'
 if (E/a/'receipt.json').exists():continue
 o,method=make(rp)
 p=o['crates/aspis-statement/src/pool_v1/pair_tree_profile.rs'];at=p.index('fn decode_pair_afterstate_boxed_v1(');assert 'kani::modifies()' in p[at-400:at]
 v=publish(a,rp,o,num%2==1,method+'; original modifies() clause retained, so the full local input frame is checked')
 if v=='OPEN':break
