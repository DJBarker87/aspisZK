from NCG_host import *
admit('NCG_SYNC002')
s=Path('/tmp/NCG_native.rs').read_text()
r=py(f"from pathlib import Path;Path({(B+'/NCG_src/crates/aspis-r1-cost-probe/src/NCG_native.rs')!r}).write_text({s!r})");assert r.returncode==0,r.stderr
