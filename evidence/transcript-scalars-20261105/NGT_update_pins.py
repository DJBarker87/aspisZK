from pathlib import Path
import json,hashlib,subprocess
E=Path(__file__).resolve().parent
r='crates/aspis-r1-cost-probe/src/sampler.rs';s=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+r]).decode();(E/'NGT_sampler_source.rs.txt').write_text(s+'\n#[cfg(kani)] #[path="NGT_sampler.rs"] mod NGT_sampler;\n')
over=json.loads((E/'NGT_OVERLAY.json').read_text());over.update({r:'NGT_sampler_source.rs.txt','crates/aspis-r1-cost-probe/src/NGT_sampler.rs':'NGT_sampler.rs.txt'});(E/'NGT_OVERLAY.json').write_text(json.dumps(over,indent=2));(E/'NGT_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256((E/p).read_bytes()).hexdigest() for n,p in over.items()},indent=2))
