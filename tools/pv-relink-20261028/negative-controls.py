"""Check that the structural token matcher rejects changed calls, order and constants."""
from common import *
s=std('std/src/path.rs');wide=(R/'crates/aspis-core/src/field/wide_exact.rs').read_text();block=(E/'block-buffer-sealed.rs.txt').read_text();ref=(R/'tools/pv-cblib-20261027/lib.rs').read_text()
cases=[('join call order',s,'fn _join(',body(s,'fn _join(').replace('let mut buf = self.to_path_buf();','let mut buf = PathBuf::new();')),
 ('join separator constant',s,'fn _push(',body(s,'fn _push(').replace('MAIN_SEPARATOR_STR','"x"')),
 ('String append primitive',std('alloc/src/string.rs'),'pub fn push_str(', '{self.vec.clear()}'),
 ('wide chunk width',wide,'pub fn to_le_bytes(',body(wide,'pub fn to_le_bytes(').replace('chunks_exact_mut(4)','chunks_exact_mut(8)')),
 ('wide limb order',wide,'pub const fn to_limbs(',body(wide,'pub const fn to_limbs(').replace('self.c0.c0.a.0','self.c1.c1.b.0')),
 ('split tail offset',block[block.index('impl Sealed for super::Eager'):],'fn split_blocks<',body(block[block.index('impl Sealed for super::Eager'):],'fn split_blocks<').replace('.add(blocks_len)','.add(0)')),
 ('String view call',s[s.index('AsRef<Path> for String'):],'fn as_ref(', '{Path::new("")}')]
rows=[]
for name,source,needle,bad in cases:
 try:checked(source,needle,bad)
 except AssertionError:rows.append(dict(mutation=name,rejected=True))
 else:raise SystemExit('structural checker failed negative control: '+name)
(E/'negative-controls.json').write_text(json.dumps(rows,indent=2)+'\n');print(len(rows),'source mutation controls rejected')
