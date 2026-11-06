from pathlib import Path
import subprocess,difflib
E=Path(__file__).resolve().parent
REV='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
def save(module,text,label):
 parent='crates/aspis-r1-cost-probe/src/candidate.rs';root='crates/aspis-r1-cost-probe/src/lib.rs'
 original=subprocess.check_output(['git','show',REV+':'+parent],text=True)
 lib=subprocess.check_output(['git','show',REV+':'+root],text=True)
 additions=[(parent,original,original+'\n#[cfg(kani)]\n#[path="'+module+'.rs"]\nmod '+module+';\n'),(root,lib,'#![cfg_attr(kani,feature(allocator_api))]\n'+lib)]
 patch=''
 for name,before,after in additions:
  patch+='diff --git a/'+name+' b/'+name+'\n'+''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+name,tofile='b/'+name))
 name='crates/aspis-r1-cost-probe/src/'+module+'.rs'
 patch+='diff --git a/'+name+' b/'+name+'\nnew file mode 100644\n'+''.join(difflib.unified_diff([],text.splitlines(True),fromfile='/dev/null',tofile='b/'+name))
 (E/(label+'.patch')).write_text(patch)
def load(label,module='NLE_auth_window',directory='crates/aspis-r1-cost-probe/src'):
 patch=(E/(label+'.patch')).read_text();needle='diff --git a/'+directory+'/'+module+'.rs '
 part=patch[patch.index(needle):];return '\n'.join(l[1:] for l in part.splitlines() if l.startswith('+') and not l.startswith('+++'))+'\n'
