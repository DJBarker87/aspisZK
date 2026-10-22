from pathlib import Path
import hashlib,json
H=Path(__file__).resolve().parent
root=Path.cwd();spans=[]
def body(file,start,end):
 p=root/file;s=p.read_text();a=s.index(start);b=s.index(end,a);text=s[a:b]
 spans.append(dict(source=file,source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),start_line=s[:a].count('\n')+1,end_line=s[:b].count('\n')+1,body_sha256=hashlib.sha256(text.encode()).hexdigest()))
 return text
pair=body('crates/aspis-core/src/r0/encoder.rs','        p0 = p0.add(pair[0].mul(n));','    }\n    (p0, p1)')
fill=body('crates/aspis-core/src/r0/basis.rs','            out[width + j] = out[j].mul(factor);','        }\n        width *= 2;')
stage=body('crates/aspis-core/src/r0/basis.rs','        width *= 2;\n        factor = double(factor);','    }\n    out')
double=body('crates/aspis-core/src/r0/basis.rs','    let square = x.mul(x);','\n}\n\n/// SPEC §3: evaluate N_j')
pair_owner=body('docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/pair-owner/lib.rs','  let n=basis[i];','  pairs(q,basis,i+1,left-1,p0,p1)')
fill_owner=body('docs/research/100bit-spend-path-20261013/evidence/prover-commit47-20261022/basis-owner/lib.rs','  out[width+j]=out[j].mul(factor);','  fill(out,j+1,left-1,width,factor)')
text='''// Generated literal native and owner iteration bodies. Loop decomposition is explicit.
fn double(x:E)->E {\n'''+double+'''\n}
fn native_pair(q:&[E;1024],basis:[E;512],i:usize,mut p0:E,mut p1:E)->(E,E) {
 // Current iterator cursor under D157 chunks_exact/zip semantics.
 let (pair,n)=q[2*i..].chunks_exact(2).zip([basis[i]]).next().unwrap();
'''+pair+''' (p0,p1)
}
fn owner_pair(q:[E;1024],basis:[E;512],i:usize,p0:E,p1:E)->(E,E) {
'''+pair_owner+''' (p0,p1)
}
fn native_fill(mut out:[E;512],width:usize,j:usize,factor:E)->[E;512] {
 assert!(j<width.min(512-width));
'''+fill+''' out
}
fn owner_fill(mut out:[E;512],width:usize,j:usize,factor:E)->[E;512] {
'''+fill_owner+''' out
}
fn native_stage(mut width:usize,mut factor:E)->(usize,E) {
'''+stage+''' (width,factor)
}
fn owner_stage(width:usize,factor:E)->(usize,E) {
 let square=factor.mul(factor);
 (width*2,square.add(square).sub(E::ONE))
}
'''
(H/'iterations.rs').write_text(text)
(H/'source-spans.json').write_text(json.dumps(dict(spans=spans,generated_sha256=hashlib.sha256(text.encode()).hexdigest()),indent=2)+'\n')
