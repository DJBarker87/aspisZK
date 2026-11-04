"""Keep generated predecessor reports in the worker's evidence directory."""
from pathlib import Path
import os
root=Path(os.environ['NGF_REPOSITORY_ROOT']);out=Path(os.environ['NGF_CHILD_REPORTS']);own=root/'evidence/slice-s-retarget3-20261104';original=Path.open

def isolated(self,mode='r',*args,**kwargs):
 if any(c in mode for c in 'wax+') and self.is_relative_to(root) and not self.is_relative_to(own):
  p=out/self.relative_to(root);p.parent.mkdir(parents=True,exist_ok=True);return original(p,mode,*args,**kwargs)
 return original(self,mode,*args,**kwargs)
Path.open=isolated
