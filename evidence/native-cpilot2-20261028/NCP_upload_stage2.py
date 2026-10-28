from pathlib import Path
import NCP_runner as m
m.admit('NCP_STAGE2_UPLOAD')
s=(m.E/'NCP_digest.rs.txt').read_text();word=(m.E/'NCP_word.rs.txt').read_text()
r=m.py(f'''from pathlib import Path
b=Path({(m.B+'/NCP_src')!r})
(b/'crates/aspis-statement/src/NCP_digest.rs').write_text({s!r})
p=b/'crates/aspis-statement/src/lib.rs';s=p.read_text();p.write_text(s.replace('#[cfg(any(kani,ncp_extract))] pub mod NCP_digest;','#[cfg(kani)] pub mod NCP_digest;'))
p=b/'crates/aspis-core/src/lib.rs';s=p.read_text();assert 'pub mod NCP_word' not in s;p.write_text(s+'\\n#[cfg(kani)] pub mod NCP_word;\\n')
(b/'crates/aspis-core/src/NCP_word.rs').write_text({word!r})
p=b/'crates/aspis-core/src/field.rs';s=p.read_text();assert 'NCP_word_ref' not in s;p.write_text(s.replace('    pub fn to_le_bytes(self) -> [u8; 4] {{','    #[cfg_attr(kani, kani::ensures(|r: &[u8;4]| *r == crate::NCP_word::NCP_word_ref(self.0)))]\\n    pub fn to_le_bytes(self) -> [u8; 4] {{'))
''');assert r.returncode==0,r.stderr
