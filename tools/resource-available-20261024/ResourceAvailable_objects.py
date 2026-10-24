"""Read only pinned git objects; never consult another worktree or host."""
import hashlib
import json
from pathlib import Path
import runpy
import subprocess
from unittest.mock import patch

ROOT=Path(__file__).resolve().parents[2]
REV='5756082d85e4d6784de4566059d6a9845604342a'
BASE='tools/resource-stat-20261024/'
ACTUAL='evidence/resource-actual-20261024/'

def sha(raw): return hashlib.sha256(raw).hexdigest()

class Objects:
    def __init__(self):
        self.cache={}; self.pins={}; self.revision=REV
        self.proc=subprocess.Popen(['git','cat-file','--batch'],cwd=ROOT,stdin=subprocess.PIPE,stdout=subprocess.PIPE)
    def read(self,path):
        if path not in self.cache:
            self.proc.stdin.write((self.revision+':'+path+'\n').encode());self.proc.stdin.flush()
            h=self.proc.stdout.readline().decode().split();assert len(h)==3,h
            raw=self.proc.stdout.read(int(h[2]));assert self.proc.stdout.read(1)==b'\n'
            self.cache[path]=raw;self.pins[path]=dict(sha256=sha(raw),size=len(raw),git_blob=h[0])
        return self.cache[path]
    def json(self,path): return json.loads(self.read(path))
    def run(self,path,*args,**kwargs):
        path=str(path)
        if path.startswith(str(ROOT)+'/'):path=path[len(str(ROOT))+1:]
        raw=self.read(path)
        env=dict(__file__=str(ROOT/path),__name__='ResourceAvailable_immutable_'+Path(path).stem)
        with patch.object(runpy,'run_path',self.run):exec(compile(raw,str(ROOT/path),'exec'),env)
        return env
    def close(self):
        self.proc.stdin.close();assert self.proc.wait()==0
