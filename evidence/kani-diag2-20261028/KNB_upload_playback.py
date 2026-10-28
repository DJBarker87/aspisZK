from KNB_host import *
admit('KNB_UPLOAD_PLAYBACK')
s=(E/'KNB_playback.rs').read_text()
r=py('from pathlib import Path\np=Path('+repr(B+'/KNB_src/crates/aspis-r1-cost-probe/src')+')\n(p/"KNB_playback.rs").write_text('+repr(s)+')\nf=p/"candidate.rs";s=f.read_text();marker=chr(10)+\'# \'\nmarker=chr(10)+\'#[cfg(test)] #[path="KNB_playback.rs"] mod KNB_playback;\'+chr(10)\nif marker not in s:f.write_text(s+marker)\n')
assert r.returncode==0,r.stderr
r=ssh('/home/dombarker/.cargo/bin/cargo-kani kani playback --help');(E/'KNB_playback_help.txt').write_text(r.stdout+r.stderr)
