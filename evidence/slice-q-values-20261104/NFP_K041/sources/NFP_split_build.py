"""Split timed-out full caller at the dot-result cut; exact source suffix."""
from pathlib import Path
import json,hashlib
B=Path(__file__).resolve().parent

def apply(f,S):
 n='crates/aspis-r1-cost-probe/src/candidate.rs'
 # The real query_values prefix remains available unchanged for prefix runs.
 full=(B/'NFP_full.rs.txt').read_text();common=full[:full.index('fn e()->E')]
 s=f[n];a=s.index('    crate::trace::value',s.index('fn query_values('));b=s.index('\n}\n',a)
 body=s[a:b]
 replacements=[('crate::trace::value(', 'NFP_query::trace('),('circle_fold_with_inverses(p.alpha[0], dots, &inverse)','NFP_query::circle(p.alpha[0],dots,&inverse,nfp)'),('core::array::from_fn(|s| field(&q[672..800], s))','core::array::from_fn(|s| NFP_query::field(&q[672..800],s,nfp))'),('line_fold_with_inverses(p.alpha[1], values, &inverse)','NFP_query::line(p.alpha[1],values,&inverse,nfp)'),('z.mul(z)','NFP_query::product(z,z,nfp)'),('accumulate_batched_with_node(p, &mut a, node, folded, &mut pending)','NFP_query::accumulate(p,&mut a,node,folded,&mut pending,nfp)')]
 # Trace replacements keep argument evaluation in source order.
 import re
 traces=re.findall(r'crate::trace::value\(([^;]+)\);',body)
 for t in traces:body=body.replace('crate::trace::value('+t+');','NFP_query::trace('+t+',nfp);')
 for old,new in replacements[1:]:assert body.count(old)==1,old;body=body.replace(old,new)
 restored=body
 for old,new in reversed(replacements[1:]):restored=restored.replace(new,old)
 for t in traces:restored=restored.replace('NFP_query::trace('+t+',nfp);','crate::trace::value('+t+');')
 assert restored==s[a:b]
 fn='''fn NFP_after_dots(q:&[u8],p:&Prepared,mut a:Accumulator,geometry:&QueryGeometry,mut pending:BatchedWeights,dots:[E;4],u:usize,obs:Observer,nfp:&mut Log)->Result<(Accumulator,BatchedWeights),Error>{
 let i=a.next;
'''+body+'\n}\n'
 harness=(B/'NFP_suffix.rs.txt').read_text()
 (S/'crates/aspis-r1-cost-probe/src/NFP_query.rs').write_text(common+fn+harness)
 return dict(suffix_erasure_exact=True,source_cut='query_values: first trace -> final return',qualification='Arbitrary local post-dot state; ambient Vec and geometry frame composition remains OPEN')
