from pathlib import Path
E=Path(__file__).resolve().parent
error='''
// Exhaustive native Error generator, no success bias or hidden postcondition.
impl kani::Arbitrary for Error{fn any()->Self{match kani::any::<u8>()%8 {0=>Error::Parse,1=>Error::Semantic,2=>Error::Transcript,3=>Error::Relation,4=>Error::Merkle,5=>Error::Query,6=>Error::Checkpoint,_=>Error::Allocation}}}
'''
for file in ['NCG_shapes.rs','NCG_install.rs']:
 p=Path('/tmp')/file;s=p.read_text();s+=error;p.write_text(s)
# The M31 public tuple carrier contains arbitrary U32, including noncanonical ones.
(E/'NCG_field_arbitrary.rs.txt').write_text('use super::M31;\nimpl kani::Arbitrary for M31 {fn any()->Self {M31(kani::any())}}\n')
p=E/'NCG_run.py';s=p.read_text();s=s.replace("base['sources'] += json.loads", "base['sources'] += json.loads")
p.write_text(s)
# Add source pins only once these files have actually been uploaded.
p=E/'NCG_batch5.py';s=p.read_text();s=s.replace("s=Path('/tmp/NCG_shapes.rs').read_text()", "s=Path('/tmp/NCG_shapes.rs').read_text()")
s=s.replace("for n,h in enumerate", ''' core=(E/'NCG_field_arbitrary.rs.txt').read_text()
 r=py(f"from pathlib import Path;p=Path({(B+'/NCG_src/crates/aspis-core/src/field.rs')!r});s=p.read_text();marker='\\\\n#[cfg(kani)] #[path=\\\"NCG_field_arbitrary.rs\\\"] mod NCG_field_arbitrary;\\\\n';p.write_text(s if marker in s else s+marker);(p.parent/'NCG_field_arbitrary.rs').write_text({core!r})");assert r.returncode==0,r.stderr
import os
os.environ['NCG_EXTRA_SOURCES']=json.dumps(['NCG_src/crates/aspis-core/src/field.rs','NCG_src/crates/aspis-core/src/NCG_field_arbitrary.rs'])
for n,h in enumerate''')
p.write_text(s)
