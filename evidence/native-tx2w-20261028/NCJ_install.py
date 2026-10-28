from NCJ_host import *
admit('NCJ_INSTALL001')
s=(E/'NCJ_weights.rs.txt').read_text()
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
