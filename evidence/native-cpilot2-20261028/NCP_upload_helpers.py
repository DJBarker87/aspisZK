import NCP_runner as m
m.admit('NCP_HELPERS_UPLOAD')
scalar=(m.E/'NCP_scalar.rs.txt').read_text();exact=(m.E/'NCP_exact.rs.txt').read_text()
r=m.py(f'''from pathlib import Path
b=Path({(m.B+'/NCP_src')!r});base=b/'crates/aspis-statement/src'
p=base/'lib.rs';p.write_text(p.read_text()+'\\n#[cfg(kani)] pub mod NCP_scalar;\\n')
(base/'NCP_scalar.rs').write_text({scalar!r})
p=base/'pool_v1/pair_terminal.rs';s=p.read_text();s=s.replace('pub enum PoolV1PairVerifierTransportErrorV1 {{','#[cfg_attr(kani, derive(kani::Arbitrary))]\\npub enum PoolV1PairVerifierTransportErrorV1 {{');s=s.replace('fn validate_verified_afterstate(', '#[cfg_attr(kani, kani::ensures(|r: &Result<(),PoolV1PairVerifierTransportErrorV1>| *r == NCP_after::NCP_after_ref(afterstate)))]\\nfn validate_verified_afterstate(');s=s.replace('    while level < afterstate.next_frontier.len() {{','    #[cfg_attr(kani, kani::loop_invariant(level<=20 && NCP_after::NCP_after_prefix(afterstate,level)))]\\n    while level < afterstate.next_frontier.len() {{');s=s.replace('fn exact<const N:', '#[cfg_attr(kani, kani::ensures(|r: &Result<[u8;N],PoolV1PairVerifierTransportErrorV1>| *r == NCP_after::NCP_exact_ref::<N>(bytes)))]\\nfn exact<const N:');p.write_text(s+'\\n#[cfg(kani)] mod NCP_after;\\n')
p=base/'pool_v1/pair_terminal/NCP_after.rs';p.parent.mkdir(exist_ok=True);p.write_text({exact!r})
p=base/'pool_v1/pair_tree_profile.rs';s=p.read_text();s=s.replace('pub(crate) fn digest_is_canonical(value:', '#[cfg_attr(kani, kani::ensures(|r: &bool| *r == crate::NCP_scalar::NCP_canon(value)))]\\npub(crate) fn digest_is_canonical(value:');needle='    while i < value.len() {{';assert needle in s;s=s.replace(needle,'    #[cfg_attr(kani, kani::loop_invariant(i<=8 && crate::NCP_scalar::NCP_canon_prefix(value,i)))]\\n'+needle,1);p.write_text(s)
''');assert r.returncode==0,r.stderr
