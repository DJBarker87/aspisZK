from pathlib import Path
import subprocess,json,hashlib
D=Path('/home/dombarker/project-offloads/codex-pv-rdeac-20261028');N=D/'native02';N.mkdir(exist_ok=True)
R=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu')
cmd=[str(R/'bin/rustc'),'--edition=2021','-Copt-level=3','-Cdebug-assertions=false','-Coverflow-checks=false','-Cpanic=unwind',f'--emit=link={N}/owned-join,mir={N}/owned-join.mir',str(D/'owned-join.rs')]
print('Expected time: optimized fixture compilation then finite allocation/deallocation validation.',flush=True)
subprocess.run(cmd,check=True)
p=subprocess.run([str(N/'owned-join')],capture_output=True,text=True);print(p.stdout,flush=True);print(p.stderr,flush=True);assert p.returncode==0,p
lib=R/'lib/rustlib/src/rust/library';files=[lib/'std/src/path.rs',lib/'alloc/src/vec/mod.rs',lib/'alloc/src/raw_vec/mod.rs',lib/'alloc/src/string.rs']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
mir=(N/'owned-join.mir').read_text()
# Preserve every owned wrapper cleanup block, not just a passing value assertion.
body=mir[mir.index('fn owned('):mir.index('fn borrowed(')]
assert 'drop(_2)' in body,body
(N/'owned-wrapper.mir.txt').write_text(body)
(N/'result.json').write_text(json.dumps(dict(classification='finite native validation; std-only fixture of deployed library bodies, not complete endpoint/binary equivalence',command=cmd,toolchain=subprocess.check_output([str(R/'bin/rustc'),'-vV'],text=True),source_sha256=sha(D/'owned-join.rs'),binary_sha256=sha(N/'owned-join'),mir_sha256=sha(N/'owned-join.mir'),library_sources=[dict(path=str(f),sha256=sha(f)) for f in files],features='No project dependencies; deployed feature graph inherited from pv-rdb1/resolved-features.json for source-site correspondence only',stdout=p.stdout,exit=p.returncode,owned_wrapper=body),indent=2)+'\n')
