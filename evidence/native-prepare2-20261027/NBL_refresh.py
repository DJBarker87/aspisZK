from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent
n='crates/aspis-r1-cost-probe/src/candidate.rs'
old=subprocess.check_output(['git','show','4bb3b3f5:'+n]).decode();new=old+'\n#[cfg(kani)]\nmod NBL_candidate;\n'
s=Path('/private/tmp/NBL_candidate.rs').read_text();rel='crates/aspis-r1-cost-probe/src/NBL_candidate.rs'
p=''.join(difflib.unified_diff(old.splitlines(keepends=True),new.splitlines(keepends=True),fromfile='a/'+n,tofile='b/'+n))
p+='--- /dev/null\n+++ b/'+rel+'\n@@ -0,0 +1,'+str(len(s.splitlines()))+' @@\n'+''.join('+'+line for line in s.splitlines(keepends=True))
(E/'NBL_harness.patch').write_text(p)
