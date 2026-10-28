"""Own local admission guard, shared by this lane's two transport wrappers.
No shared launcher, host reservation, cgroup, or global lock is changed.
"""
from pathlib import Path
import json,os
class ActiveRun:
 def __init__(self,e,attempt,kind):
  self.path=Path(e)/'NCK_ACTIVE.json';self.e=Path(e)
  if self.path.exists():
   old=json.loads(self.path.read_text())
   try:os.kill(old['pid'],0)
   except ProcessLookupError:alive=False
   else:alive=True
   assert not alive,('own wrapper is still active',old)
   assert not old.get('submitted') or (self.e/old['attempt']/'receipt.json').is_file(),('unresolved submitted attempt; recover read-only first',old)
   self.path.unlink()
  self.row=dict(attempt=attempt,kind=kind,pid=os.getpid(),submitted=False)
  with self.path.open('x') as f:json.dump(self.row,f)
 def submitted(self):
  self.row['submitted']=True;self.path.write_text(json.dumps(self.row)+'\n')
 def terminal(self):
  assert (self.e/self.row['attempt']/'receipt.json').is_file()
  assert json.loads(self.path.read_text())['pid']==os.getpid()
  self.path.unlink()
