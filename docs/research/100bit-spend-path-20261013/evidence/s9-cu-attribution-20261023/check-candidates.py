#!/usr/bin/env python3
from pathlib import Path
import hashlib,json
p=Path(__file__).resolve().parent
for label in ['C','H5','H11','H12']:
 b=p/'retained-attempts'/label
 r=json.loads((b/'gates/sbf/receipt.json').read_text())
 for rel in ['crates/aspis-r1-cost-probe/src/weights.rs','crates/aspis-r1-cost-probe/src/fast_pairing.rs','programs/r1-cost-probe/src/r1_pool_adapter_owned.rs']:
  q=b/'work/src'/rel
  if not q.exists(): q=b/'sources'/Path(rel).name
  assert hashlib.sha256(q.read_bytes()).hexdigest()==r['admitted_source_hashes'][rel],(label,rel)
f='work/src/crates/aspis-r1-cost-probe/src/fast_pairing.rs'
a=(p/'retained-attempts/H5/sources/fast_pairing.rs').read_text()
old='pub fn finish(self)->Q {Q([reduce(self.sums[0]),reduce(self.sums[1]),reduce(self.sums[2]),reduce(self.sums[3])])}'
assert a.count(old)==1
assert (p/'retained-attempts/H11'/f).read_text()==a.replace(old,'pub fn finish(self)->Q {Q(self.sums.map(reduce))}')
assert (p/'retained-attempts/H12'/f).read_text()==a.replace(old,'pub fn finish(self)->Q {let [a,b,c,d]=self.sums; Q([reduce(a),reduce(b),reduce(c),reduce(d)])}')
print('Exact retained source hashes and single-method H11/H12 deltas checked.')
