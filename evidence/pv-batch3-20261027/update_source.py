from pathlib import Path
import subprocess,hashlib,json,sys
D=Path('evidence/pv-batch3-20261027');old=json.loads((D/'forest-source.json').read_text());files=set(old['files']);files.update(subprocess.check_output(['git','ls-files','--','crates','programs','xtask']).decode().splitlines());files.discard('crates/aspis-r1-cost-probe/src/host_forest.rs');files.add('crates/aspis-prover/src/host_forest.rs');files.add('docs/research/v8-r0-zk-20261009/refine/diffharness/tests/glue_gen.rs');files=sorted(files)
manifest=dict(revision=subprocess.check_output(['git','rev-parse','HEAD']).decode().strip(),files={p:hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in files})
(D/('source-'+sys.argv[1]+'.json')).write_text(json.dumps(manifest,indent=2)+'\n')
changed=[p for p in files if old['files'].get(p)!=manifest['files'][p]]
(D/'changed-files.txt').write_text('\n'.join(changed)+'\n')
