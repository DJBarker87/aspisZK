from NCJ_host import *
admit('NCJ_SETUP003')
patch=(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
(E/'NCJ_KMX_SHA256.txt').write_text(hashlib.sha256(patch.encode()).hexdigest()+'\n')
r=py(f'''from pathlib import Path
import subprocess
b=Path({B!r});s=b/'NCJ_src';p=b/'NCJ_KMX_copy_stubs.patch';p.write_text({patch!r})
r=subprocess.run(['git','apply',str(p)],cwd=s,capture_output=True,text=True);assert r.returncode==0,r.stdout+r.stderr
p=s/'crates/aspis-r1-cost-probe/src/lib.rs';t=p.read_text();p.write_text(t.replace('#![no_std]','#![no_std]\\n#![cfg_attr(kani,feature(allocator_api))]')+'\\n#[cfg(kani)] #[path="../../../KMX_stubs.rs"] pub mod KMX_stubs;\\n')
''');assert r.returncode==0,r.stderr
cfg=dict(attempt='NCJ_FROZEN_GRAPH',kind='metadata',sources=['NCJ_src/Cargo.lock','NCJ_src/Cargo.toml'],command=['/home/dombarker/.cargo/bin/cargo','metadata','--manifest-path',B+'/NCJ_src/Cargo.toml','--locked','--offline','--format-version','1'],timeout=120,source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),source_tree_dirty=True,env={'CARGO_NET_OFFLINE':'true','PATH':'/home/dombarker/.cargo/bin:/usr/bin:/bin'},deps_fingerprint={'frozen_revision':'4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'},expected_time='frozen metadata only; no compile or proof')
r=launch(cfg);assert r['exit_status']==0
m=json.loads(next(l for l in (E/'NCJ_FROZEN_GRAPH/stdout.log').read_text().splitlines() if l.startswith('{')))
keys={p['id']:json.dumps([p['name'],p['version'],p.get('source')],separators=(',',':')) for p in m['packages']}
graph={'packages':sorted(keys.values()),'edges':sorted([keys[n['id']],sorted(keys[d] for d in n['dependencies'])] for n in m['resolve']['nodes'])}
(E/'NCJ_frozen_graph.json').write_text(json.dumps(graph,indent=2)+'\n')
