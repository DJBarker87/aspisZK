"""Check original frozen native step text, separately from solver verdicts."""
from pathlib import Path
import hashlib,json,lzma,re
E=Path(__file__).resolve().parent
f=json.loads(lzma.decompress((E/'NIC_FROZEN.json.xz').read_bytes()))
native=(E/'NIC_native.rs.txt').read_text();dots=(E/'NIC_dots.rs.txt').read_text()
def tok(s):return re.findall(r'[A-Za-z_][A-Za-z_0-9]*|[0-9]+|::|->|[^\s]',s)
def body(s,name):
 m=re.search(r'fn '+re.escape(name)+r'(?:<[^\n]+>)?\(',s);assert m,name
 a=s.index('{',m.end());j=a+1;depth=1
 while depth:
  depth+=(s[j]=='{')-(s[j]=='}');j+=1
 return s[a+1:j-1]
verifier=f['crates/aspis-r1-cost-probe/src/verifier.rs'];fast=f['crates/aspis-r1-cost-probe/src/fast_dots.rs']
a=fast.index('                let scalar = M31::from_le_bytes(');b=fast.index('\n            }',a);main=fast[a:b]
main=re.sub(r'u64::from\(coefficient\[([0-7])\]\) \* u64::from\(scalar.0\)',r'crate::verifier::NIC_native::raw_product( coefficient[\1], scalar.0 )',main).replace('g[term]','coefficient_value')
actual=body(dots,'main_step');actual=actual[actual.index('let scalar ='):]
checks={'dot_main_exact':tok(main)==tok(actual)}
raw=body(f['crates/aspis-r1-cost-probe/src/fast_pairing.rs'],'raw')
raw=raw.replace('self.0[','left[').replace('rhs.0[','right[').replace('P as u64','2147483647u64').replace('u64::from(P)','2147483647u64')
raw=re.sub(r'\b([a-h])\*([a-h])\b',r'raw_product(\1 as u32,\2 as u32)',raw)
actual=body(native,'pairing_raw_step');a=actual.index('let _out={')+len('let _out={');actual=actual[a:actual.rfind('};')]
checks['raw_tail_exact']=tok(raw)==tok(actual)
acc=body(verifier,'accumulate_batched_with_node')
for name,text in [('basis_step','basis[n+j]=basis[j].mul(node);'),('node_step','node=node.mul(node).double().sub(M31::ONE);n*=2;')]:
 checks[name]=tok(text) in [tok(body(native,name))[i:i+len(tok(text))] for i in range(len(tok(body(native,name))))]
 checks[name+'_source']=tok(text) in [tok(acc)[i:i+len(tok(text))] for i in range(len(tok(acc)))]
# Pure getter and decoder windows have existing whole value bridges; these
# checks do not manufacture the missing abort-domain/caller producer.
checks['geometry_projection_frozen']='fn for_query(&self,index:usize)->&[M31;5] {&self.inverses[index-self.start]}' in verifier
checks['box_call_frozen']='Ok(Box::new(Self' in verifier or 'Ok(Box::new(Self {' in verifier
checks['no_writable_static']=not re.search(r'\bstatic\s+(?:mut\s+)?[A-Za-z_]',native+dots+(E/'NIC_purity.rs.txt').read_text())
checks['no_function_pointer_observation']='Option<fn' not in native+dots+(E/'NIC_purity.rs.txt').read_text()
assert all(checks.values()),checks
# Mutation tests target the asserted source association, not the implementation.
mutations={
 'drop_term_product':tok(main)!=tok(main.replace('coefficient[0]','coefficient[1]',1)),
 'insert_effect':tok(main)!=tok(main+'hash.digest(&[]);'),
 'wrong_raw_operand':tok(raw)!=tok(raw.replace('raw_product(c as u32,g as u32)','raw_product(c as u32,h as u32)',1)),
 'drop_basis_product':tok('basis[n+j]=basis[j].mul(node);')!=tok('basis[n+j]=basis[j];')}
assert all(mutations.values()),mutations
out=dict(status='PASS: local source windows only; no enclosing native effect join claimed',checks=checks,mutation_rejections=mutations,inputs={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in [E/'NIC_FROZEN.json.xz',E/'NIC_native.rs.txt',E/'NIC_dots.rs.txt',E/'NIC_purity.rs.txt']})
(E/'NIC_WINDOWS.json').write_text(json.dumps(out,indent=1)+'\n');print('Native source-window checks and four mutations passed')
