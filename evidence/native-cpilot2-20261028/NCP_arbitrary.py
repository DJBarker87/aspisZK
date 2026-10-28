import NCP_runner as m
from pathlib import Path
m.admit('NCP_ARBITRARY_UPLOAD')
core='impl kani::Arbitrary for crate::field::M31 { fn any()->Self {Self(kani::any::<u32>())} }\n'
err='''impl kani::Arbitrary for AtomicStatementError {fn any()->Self {let tag:u8=kani::any();kani::assume(tag<7);match tag {0=>Self::NonCanonicalDigest,1=>Self::NonCanonicalAssetId,2=>Self::FeeOutOfRange,3=>Self::PathDepthMismatch,4=>Self::InsertionIndexOutOfRange,5=>Self::CurrentAnchorMismatch,_=>Self::OutputAnchorMismatch}}}\n'''
p=m.E/'NCP_digest.rs.txt';s=p.read_text();assert 'impl kani::Arbitrary' not in s;p.write_text(s+'\n'+err)
(m.E/'NCP_arbitrary.rs.txt').write_text(core)
r=m.py(f'''from pathlib import Path
b=Path({(m.B+'/NCP_src')!r})
p=b/'crates/aspis-core/src/lib.rs';s=p.read_text();assert 'NCP_arbitrary' not in s;p.write_text(s+'\\n#[cfg(kani)] mod NCP_arbitrary;\\n')
(b/'crates/aspis-core/src/NCP_arbitrary.rs').write_text({core!r})
(b/'crates/aspis-statement/src/NCP_digest.rs').write_text({(s+'\n'+err)!r})
''');assert r.returncode==0,r.stderr
