"""Full caller instrumentation, exact frozen erasure; no new production body."""
from pathlib import Path
import json,hashlib,difflib
B=Path(__file__).resolve().parent

def apply(f,S):
 n='crates/aspis-r1-cost-probe/src/candidate.rs';s=f[n]
 old='geometry: &QueryGeometry, mut pending: BatchedWeights) -> Result<(Accumulator, BatchedWeights), Error> {'
 new=old.replace('mut pending: BatchedWeights)', 'mut pending: BatchedWeights, #[cfg(kani)] nfp: &mut NFP_query::Log)')
 assert s.count(old)==1;s=s.replace(old,new);edits=[(old,new)]
 replacements=[('crate::fast_dots::four_dots(q, g)','NFP_query::dots(q,g,nfp)'),('circle_fold_with_inverses(p.alpha[0], dots, &inverse)','NFP_query::circle(p.alpha[0], dots, &inverse,nfp)'),('core::array::from_fn(|s| field(&q[672..800], s))','core::array::from_fn(|s| NFP_query::field(&q[672..800], s,nfp))'),('line_fold_with_inverses(p.alpha[1], values, &inverse)','NFP_query::line(p.alpha[1], values, &inverse,nfp)'),('z.mul(z)','NFP_query::product(z,z,nfp)'),('accumulate_batched_with_node(p, &mut a, node, folded, &mut pending)','NFP_query::accumulate(p, &mut a, node, folded, &mut pending,nfp)')]
 a=s.index('fn query_values(');b=s.index('\n\n\n',a)
 body=s[a:b]
 for old,new in replacements:
  assert body.count(old)==1,old;body=body.replace(old,new);edits.append((old,new))
 import re
 traces=re.findall(r'crate::trace::value\(([^;]+)\);',body);assert len(traces)==6
 for t in traces:
  old='crate::trace::value('+t+');';new='NFP_query::trace('+t+',nfp);';body=body.replace(old,new);edits.append((old,new))
 s=s[:a]+body+s[b:]
 old='state = query_values(proof, p, a, g, obs, geometry, pending);';new=old.replace('geometry, pending)', 'geometry, pending, #[cfg(kani)] &mut NFP_query::Log::unused())');s=s.replace(old,new);edits.append((old,new))
 restored=s
 for old,new in reversed(edits):restored=restored.replace(new,old)
 assert restored==f[n],'full caller erasure failed'
 s+='\n#[cfg(kani)] mod NFP_query;\n';(S/n).write_text(s)
 (S/'crates/aspis-r1-cost-probe/src/NFP_query.rs').write_text((B/'NFP_full.rs.txt').read_text())
 return dict(full_erasure_exact=True,call_substitutions=edits,qualification='Full caller G on restricted ambient carrier fixtures; array/Vec frame lifting and callee installation remain OPEN')
