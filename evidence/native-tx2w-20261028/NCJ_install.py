from NCJ_host import *
admit('NCJ_INSTALL001')
# Reconstruct the historical source from its committed patch.
patch=(E/'NCJ_stage1.patch').read_text()
part=patch.split('+++ b/crates/aspis-r1-cost-probe/src/NCJ_weights.rs\n',1)[1]
s=''
for line in part.splitlines(True):
 if line.startswith('--- '):break
 if line.startswith('+'):s+=line[1:]
r=py(f'''from pathlib import Path
b=Path({B!r});s=b/'NCJ_src';p=s/'crates/aspis-r1-cost-probe/src/weights.rs'
p.write_text(p.read_text()+'\\n#[cfg(kani)] mod NCJ_weights;\\n')
(s/'crates/aspis-r1-cost-probe/src/weights/NCJ_weights.rs').parent.mkdir(exist_ok=True)
(s/'crates/aspis-r1-cost-probe/src/weights/NCJ_weights.rs').write_text({s!r})
# Path attribute keeps the source in its lane-prefixed sibling.
p.write_text(p.read_text().replace('#[cfg(kani)] mod NCJ_weights;','#[cfg(kani)] #[path="NCJ_weights.rs"] mod NCJ_weights;'))
(s/'crates/aspis-r1-cost-probe/src/NCJ_weights.rs').write_text({s!r})
(s/'crates/aspis-r1-cost-probe/src/weights/NCJ_weights.rs').unlink()
''');assert r.returncode==0,r.stderr
