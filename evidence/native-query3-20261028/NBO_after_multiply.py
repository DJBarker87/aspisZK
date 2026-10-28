from pathlib import Path
import subprocess,json,hashlib
E=Path(__file__).resolve().parent;s=(E/'NBO_native.rs.txt').read_text()
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
source=subprocess.check_output(['git','show',frozen+':crates/aspis-r1-cost-probe/src/candidate.rs'],text=True)
a=source.index('    let node = z.mul(z).double().sub(M31::ONE);',source.index('fn query_values('));b=source.index('\n}',a)
original=source[a:b];tail=original.replace('z.mul(z)','square')
s+='''
// Actual continuation AFTER the pure scalar multiplication returns.
// square is that reached return, not a field-operation stub.
fn NBO_after_square(p:&Prepared,mut a:Accumulator,mut pending:BatchedWeights,
 square:M31,folded:E,i:usize,obs:Observer)->Result<(Accumulator,BatchedWeights),Error>{
'''+tail+'''
}
'''
start=s.index('fn NBO_actual_query_accept() {');end=s.index('\n}',start)+2
case=s[start:end].replace('fn NBO_actual_query_accept()', 'fn NBO_after_square_context()')
case=case.replace('kani::assume(folded==values[(u%4)as usize]);', '''let square:u32=kani::any();kani::assume(square<2147483647);
 unsafe{NBO_EVENT=9;NBO_LINE_CALLS=1;NBO_MUL_CALLS=1;NBO_MUL_X=M31(z);NBO_MUL_Y=M31(z);NBO_MUL_OUT=M31(square);}''')
case=case.replace('query_values(&proof,&p,a,&g,None,&geometry,pending).unwrap()', 'NBO_after_square(&p,a,pending,M31(square),unsafe{NBO_LINE},next,None).unwrap()')
# This is a new after-call prestate gate. It executes no field multiply.
s+='''#[kani::proof]
#[kani::unwind(4096)]
#[kani::stub(crate::verifier::accumulate_batched_with_node,NBO_accumulate)]
'''+case+'\n'
(E/'NBO_native.rs.txt').write_text(s)
(E/'NBO_AFTER_MULTIPLY_ASSOCIATION.json').write_text(json.dumps(dict(frozen_revision=frozen,original=original,factored=tail,original_sha256=hashlib.sha256(original.encode()).hexdigest(),factored_sha256=hashlib.sha256(tail.encode()).hexdigest(),changes=['replace the reached pure z.mul(z) return with square argument','pass same p/a/pending/line/i/observer cut carriers'],claim='post-multiplication native continuation only; NOT a full-query pass, NOT a multiplication stub'),indent=2)+'\n')
