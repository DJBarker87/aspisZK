"""Lane source-hook construction; frozen production bytes are untouched."""
from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def frozen(p):return subprocess.check_output(['git','show',REV+':'+p],text=True)
def program(body,name):
 p='programs/r1-cost-probe/src/r1_pool_adapter.rs';f=frozen(p);changed=f+'\n#[cfg(kani)]\n#[path="'+name+'.rs"]\nmod '+name+';\n'
 patch=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p))+'--- /dev/null\n+++ b/programs/r1-cost-probe/src/'+name+'.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines())
 p='programs/r1-cost-probe/src/lib.rs';f=frozen(p);changed='#![cfg_attr(kani, feature(allocator_api))]\n'+f+'\n#[cfg(kani)]\nextern crate alloc;\n#[cfg(kani)]\n#[path="../../../KMX_stubs.rs"]\npub mod NEX_KMX;\n'
 patch+=''.join(difflib.unified_diff(f.splitlines(True),changed.splitlines(True),fromfile='a/'+p,tofile='b/'+p));(E/'NEX_native_contracts.patch').write_text(patch)
def helpers():
 p=(E.parent/'slice-s-compose7-20261103/NEU_K003-NEU_native_contracts.patch').read_text().split('+++ b/programs/r1-cost-probe/src/NEU_emit.rs\n',1)[1].split('--- a/',1)[0]
 s='\n'.join(l[1:] for l in p.splitlines() if l.startswith('+'))+'\n';return s[:s.index('fn construction(')]
