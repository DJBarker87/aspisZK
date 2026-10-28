import NCP_runner as m
m.admit('NCP_REFINE_HELPERS_UPLOAD')
r=m.py(f'''from pathlib import Path
p=Path({(m.B+'/NCP_src/crates/aspis-statement/src/pool_v1/pair_terminal.rs')!r});s=p.read_text()
needle='#[cfg_attr(kani, kani::ensures(|r: &Result<[u8;N],PoolV1PairVerifierTransportErrorV1>|'
assert needle in s;s=s.replace(needle,'#[cfg_attr(kani, kani::requires(bytes.len()<=33))]\\n'+needle)
needle='    let mut level = 0;';assert needle in s;s=s.replace(needle,'    #[cfg(kani)] let NCP_invariant_after = afterstate;\\n'+needle,1)
s=s.replace('NCP_after::NCP_after_prefix(afterstate,level)','NCP_after::NCP_after_prefix(NCP_invariant_after,level)');p.write_text(s)
''');assert r.returncode==0,r.stderr
