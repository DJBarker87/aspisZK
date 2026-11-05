"""Create only NGQ-owned frozen scratch inputs; no repository source writes."""
from pathlib import Path
import subprocess,json,lzma,hashlib,difflib
E=Path(__file__).resolve().parent;H='dombarker@100.108.41.90';B='/home/dombarker/project-offloads/codex-cx-transcript-queries-20261105'
frozen=json.loads(lzma.decompress((E/'NGQ_FROZEN_INPUTS.json.xz').read_bytes()));files=dict(frozen)
patch=(E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_text()
# Materialize the EXACT new-file KMX patch contents without writing a competing stub.
for part in patch.split('diff --git ')[1:]:
 head,*ls=part.splitlines();name=head.split(' b/')[1]
 files[name]='\n'.join(l[1:] for l in ls if l.startswith('+') and not l.startswith('+++'))+'\n'
p='crates/aspis-core/src/lib.rs';files[p]=files[p].replace('#![no_std]','#![cfg_attr(kani, feature(allocator_api))]\n#![no_std]')+'\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod KMX_stubs;\n'
p='crates/aspis-core/src/r0_transcript.rs';files[p]+='\n#[cfg(kani)]\n#[path="NGQ_harness.rs"]\nmod NGQ_harness;\n'
files['crates/aspis-core/src/NGQ_harness.rs']=(E/'NGQ_core_harness.rs.txt').read_text()
p='crates/aspis-r1-cost-probe/src/lib.rs';files[p]=files[p].replace('#![no_std]','#![cfg_attr(kani, feature(allocator_api))]\n#![no_std]')+'\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod KMX_stubs;\n'
p='crates/aspis-r1-cost-probe/src/transcript.rs';files[p]+='\n#[cfg(kani)]\n#[path="NGQ_pairs.rs"]\nmod NGQ_pairs;\n'
files['crates/aspis-r1-cost-probe/src/NGQ_pairs.rs']=(E/'NGQ_pairs_harness.rs.txt').read_text()
files['crates/aspis-r1-cost-probe/src/transcript.rs']+='\n#[cfg(kani)]\n#[path="NGQ_tail.rs"]\nmod NGQ_tail;\n'
files['crates/aspis-r1-cost-probe/src/NGQ_tail.rs']=(E/'NGQ_tail_harness.rs.txt').read_text()
files['crates/aspis-r1-cost-probe/src/transcript.rs']+='\n#[cfg(kani)]\n#[path="NGQ_absorb.rs"]\nmod NGQ_absorb;\n'
files['crates/aspis-r1-cost-probe/src/NGQ_absorb.rs']=(E/'NGQ_absorb_harness.rs.txt').read_text()
files['crates/aspis-r1-cost-probe/src/transcript.rs']+='\n#[cfg(kani)]\n#[path="NGQ_init.rs"]\nmod NGQ_init;\n'
files['crates/aspis-r1-cost-probe/src/NGQ_init.rs']=(E/'NGQ_init_harness.rs.txt').read_text()
files['crates/aspis-r1-cost-probe/src/transcript.rs']+='\n#[cfg(kani)]\n#[path="NGQ_call.rs"]\nmod NGQ_call;\n'
files['crates/aspis-r1-cost-probe/src/NGQ_call.rs']=(E/'NGQ_call_harness.rs.txt').read_text()
files['crates/aspis-core/src/r0_transcript.rs']+='\n#[cfg(kani)]\n#[path="NGQ_iterator.rs"]\nmod NGQ_iterator;\n'
files['crates/aspis-core/src/NGQ_iterator.rs']=(E/'NGQ_iterator_harness.rs.txt').read_text()
raw=''.join(''.join(difflib.unified_diff(frozen.get(p,'').splitlines(True),t.splitlines(True),fromfile='a/'+p,tofile='b/'+p)) for p,t in files.items() if frozen.get(p)!=t)
(E/'NGQ_HARNESSES.patch').write_text(raw)
(E/'NGQ_SOURCE_PINS.json').write_text(json.dumps({p:hashlib.sha256(t.encode()).hexdigest() for p,t in files.items()},indent=1)+'\n')
# Admission before uploading scratch inputs. Exit 78/allowed:false requires retry by caller.
script=f'''from pathlib import Path
import subprocess,json,sys
b=Path({B!r});p=b/'NGQ_SETUP-reservation.json'
with (b/'NGQ_SETUP-barrier.log').open('w') as f:r=subprocess.run(['python3','/home/dombarker/project-offloads/codex-cx-s2h-20261023/S2H_reservation.py',str(p)],stdout=f,stderr=subprocess.STDOUT)
print(p.read_text() if p.exists() else 'MISSING');sys.exit(r.returncode)
'''
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3'],input=script,text=True,capture_output=True)
(E/'NGQ_SETUP-barrier.log').write_text(r.stdout+r.stderr);ad=json.loads(r.stdout);assert r.returncode==0 and ad.get('allowed') is True,(r.returncode,ad)
script=f'''from pathlib import Path
import json
b=Path({B!r})/'NGQ_src';files=json.loads({json.dumps(files)!r})
for n,t in files.items():
 p=b/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_text(t)
print(len(files))
'''
r=subprocess.run(['ssh','-o','ControlMaster=no',H,'python3'],input=script,text=True,capture_output=True);print(r.stdout,r.stderr);assert r.returncode==0
