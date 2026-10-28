"""Materialize the patch-only harness outside the repository for transfer."""
from pathlib import Path
E=Path(__file__).resolve().parent

def source(rel='crates/aspis-r1-cost-probe/src/NBA_verifier.rs'):
 marker='+++ b/'+rel+'\n'
 tail=(E/'NBA_harness.patch').read_text().split(marker,1)[1]
 tail=tail.split('--- ',1)[0]
 return ''.join(line[1:] for line in tail.splitlines(keepends=True) if line.startswith('+'))

def path(rel='crates/aspis-r1-cost-probe/src/NBA_verifier.rs'):
 p=Path('/private/tmp/NBA_native_prepare1')/Path(rel).name
 p.parent.mkdir(exist_ok=True)
 p.write_text(source(rel))
 return p
