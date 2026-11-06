from pathlib import Path
import subprocess,json,lzma,hashlib
E=Path(__file__).resolve().parent
def read(p):
 return subprocess.check_output(['git','show','HEAD:'+p])
def inputs(a='NJD_K001'):
 root='evidence/slice-d-entry8-20261107/'
 idx=json.loads(read(root+'NJD_INPUTS.json'));out={}
 for n,h in idx['attempts'][a].items():
  raw=lzma.decompress(read(root+idx['objects'][h]['path']));assert hashlib.sha256(raw).hexdigest()==h;out[n]=raw.decode()
 return out
if __name__=='__main__':
 x=inputs();print('files',list(x));print(x['NIJ_gate.py']);print(x['NIJ_erasure.py'])
