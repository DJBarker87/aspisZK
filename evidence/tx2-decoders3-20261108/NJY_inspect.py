from pathlib import Path
import json,lzma,hashlib
Q=Path(__file__).resolve().parent.parent/'tx2-decoders2-20261108'
def inputs(a):
 idx=json.loads((Q/'NJQ_INPUTS.json').read_text());out={}
 for name,h in idx['attempts'][a].items():
  raw=lzma.decompress((Q/idx['objects'][h]['path']).read_bytes());assert hashlib.sha256(raw).hexdigest()==h;out[name]=raw.decode()
 return out
if __name__=='__main__':
 x=inputs('NJQ_K006')
 for name in ['NIJ_gate.py','NIJ_erasure.py']:
  print(name);print(x[name])
