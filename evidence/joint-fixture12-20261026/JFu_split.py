"""Permanent bounded replacement for the retired row25 hash monolith."""
from pathlib import Path
import json,sys
P=Path(__file__).resolve().parent;R=P.parents[1];old=R/'evidence/joint-fixture11-20261026/JFm_UNCHECKED'
files={};groups=[]
files[R/'lean/JFu_Q25Block00.lean']=(old/'JFm_Q25Block00.lean.txt').read_text().replace('JFm_Q25Absorb','JFu_Q25Absorb')
for start in range(1,59,8):
 end=min(start+8,59);name=f'JFu_Q25Window{start:02}';text='import JFp_SHABlocks\nset_option autoImplicit false\n'
 for i in range(start,end):
  s=(old/f'JFm_Q25Block{i:02}.lean.txt').read_text().replace('JFm_Q25Absorb','JFu_Q25Absorb');text+='\n'+s[s.index('namespace AspisR1.'):]
 files[R/'lean'/(name+'.lean')]=text;groups.append(dict(module=name,blocks=end-start,range=[start,end-1],rounds=64*(end-start)))
s=(old/'JFm_Q25SplitAggregate.lean.txt').read_text();s=s[s.index('set_option'):].replace('JFm_Q25Absorb','JFu_Q25Absorb')
files[R/'lean/JFu_Q25Aggregate.lean']='import JFu_Q25Block00\n'+''.join('import '+g['module']+'\n' for g in groups)+s
files[R/'lean/JFu_Q25Reads.lean']=(old/'JFm_Q25SplitReads.lean.txt').read_text().replace('JFm_Q25SplitAggregate','JFu_Q25Aggregate').replace('JFm_Q25','JFu_Q25')
files[P/'JFu_WINDOWS_PLAN.json']=json.dumps(groups,indent=2)+'\n'
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('split preflight:',len(files),'files, 59 absorb blocks, 2 read/ratchet blocks; max 8 per module')
