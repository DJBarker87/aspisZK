"""Finite diagnostic of the exact reached FD-format expression, not a source law."""
from pathlib import Path
import hashlib,json,os,subprocess

H=Path('/home/dombarker/project-offloads/codex-pv-uc-20261029')
O=H/'final-gates/formatting-obstruction'
O.mkdir(exist_ok=True)
# N75146 stopped before compilation because rustc was absent from the scope's
# PATH. Retain and reuse that exact partial output, never hide it in a new dir.
assert not (O/'native.json').exists() and not (O/'fd-format').exists()
wallet=H/'src/tools/r1-cost-probe/src/bin/user_client/wallet.rs'
source=wallet.read_text()
expression='format!("/proc/self/fd/{fd}")'
assert source.count(expression)==1
assert 'std::fs::File::open('+expression+')' in source
program='fn path(fd:i32)->String { '+expression+' }\n'
program+='fn main() { for fd in [3i32,4i32] { println!("{}",path(fd)); } }\n'
p=O/'fd-format.rs'
if p.exists():assert p.read_text()==program
else:p.write_text(program)
rustc='/home/dombarker/.cargo/bin/rustc'
env=dict(os.environ,PATH='/home/dombarker/.cargo/bin:/usr/bin:/bin',CARGO_NET_OFFLINE='true')
command=[rustc,'+1.94.1',str(p),'--edition=2021','-C','opt-level=3',
         '-C','panic=abort','-C','overflow-checks=off','-C','debug-assertions=off',
         '-C','link-arg=-Wl,--threads=4','-o',str(O/'fd-format')]
version=subprocess.check_output([rustc,'+1.94.1','-vV'],text=True,env=env)
subprocess.run(command,check=True,env=env)
result=subprocess.run([str(O/'fd-format')],capture_output=True,check=True)
assert not result.stderr
lines=result.stdout.decode().splitlines()
assert lines==['/proc/self/fd/3','/proc/self/fd/4']
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
record=dict(status='NATIVE DIFFERENCE CONFIRMED; not a D525 wire-format mismatch',
    evidence_class='Finite validation of the exact reached formatting expression with deployed Rust standard library/compiler and release settings; no project function or full-client equivalence claim',
    command=command,rustc=version,wallet_source_sha256=sha(wallet),
    expression=expression,expression_occurrences=1,harness_source_sha256=sha(p),
    binary_sha256=sha(O/'fd-format'),binary_bytes=(O/'fd-format').stat().st_size,
    inputs=[3,4],outputs=lines,outputs_differ=lines[0]!=lines[1],
    consequence='The emitted wallet.read erases the FD in core.fmt.rt.Argument.new_display before alloc.fmt.format. A pure external formatter receiving only erased Arguments cannot reproduce both paths. Retain fmt-1 and the full-entry gate as OPEN.',
    limitations=['This validates formatting, not file opening or FD custody.',
                 'Lean no-go theorem and raw-walk axiom audit are separate.',
                 'No source, generated body, library object, translator or comparator changed.'])
(O/'native.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record,indent=2))
