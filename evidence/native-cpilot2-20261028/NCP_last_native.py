import NCP_runner as m
from pathlib import Path
m.admit('NCP_LAST_UPLOAD')
extra='''
fn NCP_after_step(afterstate:&PoolV1PairVerifiedAfterstateV1,mut level:usize)->Result<usize,PoolV1PairVerifierTransportErrorV1>{
 if !crate::pool_v1::pair_tree_profile::digest_is_canonical(&afterstate.next_frontier[level]) {return Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate);}
 level+=1;Ok(level)
}
'''
attrs='''#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
#[kani::stub_verified(crate::pool_v1::pair_tree_profile::digest_is_canonical)]
#[kani::unwind(35)]
'''
for neg in [False,True]:
 extra+='#[kani::proof]\n'+attrs+f'''fn NCP_step_{'negative' if neg else 'positive'}(){{let afterstate:PoolV1PairVerifiedAfterstateV1=kani::any();let level:usize=kani::any();kani::assume(level<20);let expected=if crate::NCP_scalar::NCP_canon(&afterstate.next_frontier[level]){{Ok(level+1)}}else{{Err(PoolV1PairVerifierTransportErrorV1::NonCanonicalAfterstate)}};assert_{'ne' if neg else 'eq'}!(NCP_after_step(&afterstate,level),expected);}}\n'''
encode='pub fn NCP_encode_prefix(out:&[u8;32],d:&Digest,n:usize)->bool {'+'&&'.join(f'(n<={i//4}||out[{i}]==(d[{i//4}].0>>{8*(i%4)}) as u8)' for i in range(32))+'}\n'
(m.E/'NCP_step.rs.txt').write_text(extra)
(m.E/'NCP_encode_prefix.rs.txt').write_text(encode)
r=m.py(f'''from pathlib import Path
b=Path({(m.B+'/NCP_src')!r});p=b/'crates/aspis-statement/src/pool_v1/pair_terminal/NCP_after.rs';p.write_text(p.read_text()+{extra!r})
p=b/'crates/aspis-statement/src/NCP_digest.rs';p.write_text(p.read_text()+{encode!r})
p=b/'crates/aspis-statement/src/atomic_statement.rs';s=p.read_text();needle='    for (index, value) in digest.iter().enumerate() {{';assert needle in s;s=s.replace(needle,'    #[cfg_attr(kani, kani::loop_invariant(kani::index<=8 && crate::NCP_digest::NCP_encode_prefix(&bytes,digest,kani::index)))]\\n'+needle,1);p.write_text(s)
''');assert r.returncode==0,r.stderr
