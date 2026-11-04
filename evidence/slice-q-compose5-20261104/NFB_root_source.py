"""Full frozen root coverage and typed source cuts; no byte is pruned silently."""
from pathlib import Path
import subprocess,hashlib,json,re
from NFB_source_checks import tok,body,REV,R,check as row_check
E=Path(__file__).resolve().parent
ROOT='crates/aspis-r1-cost-probe/src/verifier.rs::QueryGeometry::for_range'
def check(release=None,native=None):
 release=subprocess.check_output(['git','show',REV+':'+ROOT.split('::')[0]],cwd=R,text=True) if release is None else release
 native=(E/'NFB_geometry.rs.txt').read_text() if native is None else native
 row=row_check(native,release)
 f=body(release,'for_range')
 # Committed full root is a transport input, independently checked by erasures.
 assert tok(f)==tok((E/'NFB_frozen_root.rs.txt').read_text())
 prefix=body(release,'batch_prefix_products')
 assert re.search(r'fn\s+batch_prefix_products\s*\(flat\s*:\s*&\[M31\]\)\s*->\s*\(Vec<M31>,\s*M31\)',release)
 markers=['if start>end','let mut line_z_values','for &query in &queries[start..end]','if flat.is_empty()','let (prefixes,product)','let mut suffix_inverse','let mut flat_inverse','flat_inverse.resize','for i in (0..flat.len()).rev()','let inverses=','Ok(Self']
 normalized=''.join(tok(f));indices=[(normalized.rindex if m=='Ok(Self' else normalized.index)(''.join(tok(m))) for m in markers]
 assert indices==sorted(indices) and len(set(indices))==len(indices)
 spans=[]
 for k,start in enumerate(indices):
  end=indices[k+1] if k+1<len(indices) else len(normalized)
  spans.append(dict(first=markers[k],start=start,end=end,token_text_sha256=hashlib.sha256(normalized[start:end].encode()).hexdigest()))
 assert indices[0]==0 and spans[-1]['end']==len(normalized)
 for text in ['if values.iter().any(|x|*x==M31::ZERO){return Err(Error::Query);}',
 'flat.extend_from_slice(&values);line_z_values.push(line_z);',
 'flat_inverse[i]=suffix_inverse.mul(prefixes[i]);suffix_inverse=suffix_inverse.mul(flat[i]);',
 'let inverses=(0..line_z_values.len()).map(|i|core::array::from_fn(|j|flat_inverse[5*i+j])).collect();']:
  assert ''.join(tok(text)) in normalized,text
 domain=subprocess.check_output(['git','show',REV+':crates/aspis-r1-cost-probe/src/fast_domain.rs'],cwd=R,text=True)
 assert re.search(r'pub fn fibre_point\(u: FibreIndex\) -> Point<M31>',domain)
 assert re.search(r'pub fn line_node\(u: FibreIndex\) -> M31',domain)
 return dict(root=ROOT,frozen_revision=REV,root_body_sha256=hashlib.sha256(f.encode()).hexdigest(),source_cuts=spans,row=row,
  carrier='M31 throughout row/prefix/product/inverse/reverse; [M31;5] output rows',
  dispatch='CM31/QM31/WideExact alternatives statically unreachable at these exact typed calls; point internals remain in the CLOSED point child',
  trust='P6/D188 native semantic transport, option A reclassification; source checker is not a verified Rust parser/compiler')
if __name__=='__main__':print(json.dumps(check(),indent=1))
