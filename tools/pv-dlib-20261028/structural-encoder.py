"""Pin native encoder/basis control shapes for the structural field route.
This is a source-shape check; the Lean recurrence transport is separate.
"""
from pathlib import Path
import hashlib,json,re,subprocess
R=Path(__file__).resolve().parents[2];E=R/'evidence/pv-dlib-20261028'
def clean(s):return re.sub(r'/\*.*?\*/|//[^\n]*','',s,flags=re.S)
def tokens(s):return re.findall(r'::|=>|[A-Za-z_]\w*|\d+|[^\s]',clean(s))
def body(s,needle):
 s=clean(s);a=s.index('{',s.index(needle));d=0
 for i in range(a,len(s)):
  if s[i]=='{':d+=1
  elif s[i]=='}':
   d-=1
   if not d:return s[a:i+1]
 raise ValueError(needle)
expected={
'eval_pair':('crates/aspis-core/src/r0/encoder.rs','pub fn eval_pair', '''{
 let basis=basis::values::<E,512>(x); let mut p0=E::ZERO; let mut p1=E::ZERO;
 for (pair,n) in q.chunks_exact(2).zip(basis) {
 p0=p0.add(pair[0].mul(n)); p1=p1.add(pair[1].mul(n)); }
 (p0,p1)
}'''),
'eval_message':('crates/aspis-core/src/r0/encoder.rs','pub fn eval_message','''{
 let (p0,p1)=eval_pair(q,z.x); p0.add(z.y.mul(p1))
}'''),
'values':('crates/aspis-core/src/r0/basis.rs','pub(crate) fn values','''{
 let mut out=[E::ONE;N];let mut width=1;let mut factor=x;
 while width<N {for j in 0..width.min(N-width) {out[width+j]=out[j].mul(factor);}
 width*=2;factor=double(factor);} out
}'''),
'double':('crates/aspis-core/src/r0/basis.rs','pub(crate) fn double','''{
 let square=x.mul(x); square.add(square).sub(E::ONE)
}''')}
rows=[]
for n,(path,needle,exp) in expected.items():
 p=R/path;s=p.read_text();actual=body(s,needle)
 assert tokens(actual)==tokens(exp),(n,actual)
 rows.append(dict(name=n,path=path,git_blob=subprocess.check_output(['git','rev-parse','HEAD:'+path],text=True).strip(),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),body_sha256=hashlib.sha256(actual.encode()).hexdigest(),complete_body_tokens_match=True))
# Freeze the entire owned input, not only names or selected snippets.
owned=R/'tools/pv-dlib-20261028/owned-encoder.rs'
expected_owned='//! Safe owned value references. Recursion exposes bounded control without MIR loop joins.\nuse aspis_core::r0::{CodeField,domain::Point};\npub fn basis_cell<E:CodeField>(mut out:[E;512],width:usize,j:usize,factor:E)->[E;512] {\n    out[width+j]=out[j].mul(factor);out\n}\nfn basis_fill<E:CodeField>(out:[E;512],width:usize,j:usize,factor:E)->[E;512] {\n    if j<width {basis_fill(basis_cell(out,width,j,factor),width,j+1,factor)} else {out}\n}\nfn basis_round<E:CodeField>(out:[E;512],width:usize,factor:E)->[E;512] {\n    if width<512 {\n        let out=basis_fill(out,width,0,factor);\n        let square=factor.mul(factor);\n        basis_round(out,width*2,square.add(square).sub(E::ONE))\n    } else {out}\n}\npub fn basis<E:CodeField>(x:E)->[E;512] {basis_round([E::ONE;512],1,x)}\nfn encoder_fold<E:CodeField>(q:&[E;1024],basis:&[E;512],j:usize,p0:E,p1:E)->(E,E) {\n    if j<512 {\n        encoder_fold(q,basis,j+1,p0.add(q[2*j].mul(basis[j])),p1.add(q[2*j+1].mul(basis[j])))\n    } else {(p0,p1)}\n}\npub fn encoder<E:CodeField>(q:&[E;1024],p:Point<E>)->E {\n    let basis=basis(p.x);let (p0,p1)=encoder_fold(q,&basis,0,E::ZERO,E::ZERO);\n    p0.add(p.y.mul(p1))\n}\n\n'
assert tokens(owned.read_text())==tokens(expected_owned),'owned source changed'
differences=[
 dict(native='chunks_exact(2).zip(basis), forward-only',reference='index j, q[2*j], q[2*j+1], basis[j]',
      proofs=['PV_DL_EncoderPairs.coordinate','PV_DL_EncoderZip.coordinate','PV_DL_EncoderNative.fold'],
      bounds='512 complete pairs, 512 basis entries; no remainder'),
 dict(native='while/for mutable basis',reference='owned recursive basis_round/basis_fill/basis_cell',
      proofs=['PV_DL_EncoderFill.source','PV_DL_EncoderBasis.source','PV_DL_EncoderMutation.restoration','PV_DL_EncoderBounds.cells','PV_DL_EncoderBounds.target_val','PV_DL_EncoderBounds.writes'],
      bounds='width*2^fuel=512 and j+fuel=width; width+j<512'),
 dict(native='width.min(N-width)',reference='width for N=512',
      proofs=['PV_DL_EncoderBasis.half_rank','PV_DL_EncoderBasis.native_min']),
 dict(native='width*=2; native usize additions',reference='wrapping indices in extracted owned reference',
      proofs=['PV_DL_EncoderBasis.advance_val','PV_DL_EncoderRange.advance_val','PV_DL_EncoderRange.even','PV_DL_EncoderRange.odd'],
      bounds='all computed indices <1024, final width512'),
 dict(native='E::ZERO twice',reference='E::ZERO once in emission, repeated pure Result in control model',
      proofs=['PV_DL_EncoderControl.duplicate','PV_DL_EncoderControl.source_reference']),
 dict(native='basis::double(factor)',reference='mul factor factor; add square square; sub ONE',
      proofs=['PV_DL_EncoderBasis.factor','PV_DL_EncoderBasis.basis_source']),
]
j=dict(revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),native_shapes=rows,
 owned_source=dict(path=str(owned.relative_to(R)),sha256=hashlib.sha256(owned.read_bytes()).hexdigest(),all_tokens_match=True),
 differences=differences,native_link_evidence_class='structural',ruling='k (chained field arithmetic)',
 complete_result_theorem='R1Z.PV_DL_EncoderNative.source_reference',
 selected_consumption_theorem='R1Z.PV_DL_EncoderSelected.consumed',
 finite_validation='encoder-native-finite-01/receipt.json;128dense M31/QM31 plus changed-write and sparse fixtures; finite validation only',
 chained_field_arithmetic_kani=False,
 scope='structural binding of source bodies; standard forward slice chunks/zip semantics; pure CodeField Result parameters; no SHA-NI or compiler semantics claim')
(E/'encoder-native-shapes.json').write_text(json.dumps(j,indent=2)+'\n')
print('four shipped bodies and whole owned source pinned; six explicit differences with Lean transport')
