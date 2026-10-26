"""Split row26: 16 absorb compression blocks, two read/ratchet blocks."""
from pathlib import Path
import re,sys,json
P=Path(__file__).resolve().parent;R=P.parents[1]
s=(R/'evidence/joint-fixture11-20261026/JFm_UNCHECKED/JFm_Q26Hashes.lean.txt').read_text().replace('JFm_Q26','JFu_Q26')
parts=re.split(r'(?=namespace AspisR1\.JFu_Q26)',s);absorb=parts[1];blocks=re.findall(r'namespace B\d+\n.*?\nend B\d+\n',absorb,re.S);assert len(blocks)==16
files={}
for start in [0,8]:
 name=f'JFu_Q26Window{start:02}';files[R/'lean'/(name+'.lean')]='import JFp_SHABlocks\nset_option autoImplicit false\nnamespace AspisR1.JFu_Q26Absorb\nopen JFp_SHA256\n'+''.join(blocks[start:start+8])+'end AspisR1.JFu_Q26Absorb\n'
aggregate=absorb[absorb.index('theorem lenB00'):]
files[R/'lean/JFu_Q26Aggregate.lean']='import JFu_Q26Window00\nimport JFu_Q26Window08\nset_option autoImplicit false\nnamespace AspisR1.JFu_Q26Absorb\nopen JFp_SHA256\n'+aggregate
files[R/'lean/JFu_Q26Reads.lean']='import JFu_Q26Aggregate\nset_option autoImplicit false\n'+''.join(parts[2:])
source=(R/'evidence/joint-fixture11-20261026/JFm_UNCHECKED/JFm_Q26Source.lean.txt').read_text().replace('JFm_Q26','JFu_Q26').replace('JFm_Q25','JFu_Q25').replace('import JFu_Q26Hashes','import JFu_Q26Reads')
files[R/'lean/JFu_Q26Source.lean']=source
for f,t in files.items():
 if '--check' in sys.argv:assert f.read_text()==t,f
 else:f.write_text(t)
print('row26 preflight:',len(files),'files; max8 compression blocks per launch')
