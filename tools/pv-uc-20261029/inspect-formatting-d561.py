"""Read-only source provenance for formatting boundaries; no native execution."""
from pathlib import Path
import hashlib,json,shlex,subprocess
R=Path(__file__).resolve().parents[2]
program=r'''
from pathlib import Path
import hashlib,json
root=Path('/home/dombarker/.rustup/toolchains/1.94.1-x86_64-unknown-linux-gnu/lib/rustlib/src/rust/library')
specs=[(root/'alloc/src/string.rs','impl fmt::Write for String',38),
(root/'alloc/src/fmt.rs','pub fn format(',48),
(root/'std/src/macros.rs','macro_rules! println',22),
(root/'std/src/io/stdio.rs','fn print_to<T>',40),
(root/'std/src/io/stdio.rs','pub fn _print(',12),
(Path('/home/dombarker/.cargo/registry/src/index.crates.io-1949cf8c6b5b557f/serde_json-1.0.151/src/value/mod.rs'),'    fn fmt(&self, f: &mut fmt::Formatter)',42)]
rows=[]
for p,needle,count in specs:
 text=p.read_text();lines=text.splitlines();hits=[i for i,l in enumerate(lines) if needle in l]
 assert len(hits)==1,(p,needle,hits)
 i=hits[0];rows.append(dict(path=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),first_line=i+1,last_line=i+count,text='\n'.join(lines[i:i+count])+'\n'))
print(json.dumps(dict(evidence_class='Read-only deployed source inspection; not execution or formal native association',rows=rows),indent=2))
'''
r=subprocess.run(['ssh','dombarker@100.108.41.90','python3 -c '+shlex.quote(program)],capture_output=True,text=True)
assert r.returncode==0,r.stdout+r.stderr
x=json.loads(r.stdout);x['inspection_script_sha256']=hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
x['source_revision']=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip()
x['exit']=r.returncode
(R/'evidence/pv-uc-20261029/formatting-source-d561.json').write_text(json.dumps(x,indent=2)+'\n')
