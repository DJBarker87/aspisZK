from KNB_host import *
admit('KNB_UPLOAD_REPRO')
s=(E/'KNB_repro.rs').read_text()
r=py('from pathlib import Path\np=Path('+repr(B+'/KNB_src/crates/aspis-r1-cost-probe/src')+')\n(p/"KNB_repro.rs").write_text('+repr(s)+')\nf=p/"candidate.rs";s=f.read_text();marker=chr(10)+\'#[cfg(kani)] #[path="KNB_repro.rs"] mod KNB_repro;\'+chr(10)\nif marker not in s:f.write_text(s+marker)\n');assert r.returncode==0,r.stderr
