"""Scratch-only instrumentation; every frozen function body has a checked erasure."""
from pathlib import Path
import json,re,hashlib,difflib
B=Path(__file__).resolve().parent

def build():
 f=json.loads((B/'NFP_FROZEN.json').read_text());S=B/'NFP_src'
 for n,t in f.items():
  p=S/n
  if p.is_file():
   if n=='Cargo.lock':assert p.read_text()==t,'lock drift'
   else:p.write_text(t)
 # Apply the exact KMX files, without modifying the patch or inventing stubs.
 patch=(B/'NFP_KMX.patch').read_text();assert hashlib.sha256(patch.encode()).hexdigest()=='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
 for part in patch.split('diff --git ')[1:]:
  name=part.splitlines()[0].split(' b/')[1];lines=[l[1:] for l in part.splitlines() if l.startswith('+') and not l.startswith('+++')]
  (S/name).write_text('\n'.join(lines)+'\n')
 n='crates/aspis-r1-cost-probe/src/lib.rs';s=f[n].replace('#![no_std]','#![no_std]\n#![cfg_attr(kani,feature(allocator_api))]')
 s+='\n#[cfg(kani)] pub(crate) mod NFP_copy { include!(concat!(env!("CARGO_MANIFEST_DIR"),"/../../KMX_stubs.rs")); }\n';(S/n).write_text(s)
 n='crates/aspis-r1-cost-probe/src/candidate.rs';s=f[n]
 s+='\n#[cfg(kani)] mod NFP_query;\n'
 # Keep the real query_values name and all original statements. Only the
 # reached four_dots and trace boundary is instrumented, under cfg(kani).
 old='geometry: &QueryGeometry, mut pending: BatchedWeights) -> Result<(Accumulator, BatchedWeights), Error> {'
 new='geometry: &QueryGeometry, mut pending: BatchedWeights, #[cfg(kani)] nfp: &mut NFP_query::Log) -> Result<(Accumulator, BatchedWeights), Error> {'
 assert s.count(old)==1;s=s.replace(old,new)
 old='    let dots = crate::fast_dots::four_dots(q, g);'
 new='''    #[cfg(not(kani))]
    let dots = crate::fast_dots::four_dots(q, g);
    #[cfg(kani)]
    let dots = NFP_query::dots(q,g,nfp);
    #[cfg(kani)]
    { NFP_query::consume(i,u,dots,nfp); return Err(Error::Query); }
'''
 assert s.count(old)==1;s=s.replace(old,new)
 old='state = query_values(proof, p, a, g, obs, geometry, pending);'
 new='state = query_values(proof, p, a, g, obs, geometry, pending, #[cfg(kani)] &mut NFP_query::Log::unused());'
 assert s.count(old)==1;s=s.replace(old,new)
 # Erasure is exact, including original function and forwarding call names.
 restored=s.replace(new,old).replace('\n#[cfg(kani)] mod NFP_query;\n','').replace('geometry: &QueryGeometry, mut pending: BatchedWeights, #[cfg(kani)] nfp: &mut NFP_query::Log) -> Result<(Accumulator, BatchedWeights), Error> {', 'geometry: &QueryGeometry, mut pending: BatchedWeights) -> Result<(Accumulator, BatchedWeights), Error> {')
 a=restored.index('    #[cfg(not(kani))]\n    let dots');b=restored.index('    crate::trace::value',a)
 restored=restored[:a]+'    let dots = crate::fast_dots::four_dots(q, g);\n'+restored[b:]
 assert restored==f[n],'source erasure drift'
 (S/n).write_text(s)
 (S/'crates/aspis-r1-cost-probe/src/candidate').mkdir(exist_ok=True)
 (S/'crates/aspis-r1-cost-probe/src/candidate/NFP_query.rs').write_text((B/'NFP_query.rs.txt').read_text())
 changed={n:hashlib.sha256((S/n).read_bytes()).hexdigest() for n,t in f.items() if (S/n).is_file() and (S/n).read_text()!=t}
 patch=''.join(''.join(difflib.unified_diff(t.splitlines(True),(S/n).read_text().splitlines(True),fromfile='a/'+n,tofile='b/'+n)) for n,t in f.items() if (S/n).is_file() and (S/n).read_text()!=t)
 (B/'NFP_harness.patch').write_text(patch)
 return dict(erasure_exact=True,changed=changed,qualification='Prefix cut ONLY: actual frozen query_values up to dots; continuation remains OPEN')
if __name__=='__main__':print(json.dumps(build()))
