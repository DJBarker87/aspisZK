"""Bounded SHA certificates for the retained folded Merkle tree (max8 blocks/module).
Uses inherited JFm certificate emitter verbatim as a function, no old generator execution.
"""
from pathlib import Path
import json,sys,hashlib,re
P=Path(__file__).resolve().parent;R=P.parents[1]
base=(R/'evidence/joint-fixture11-20261026/JFm_generate.py').read_text().split('raw=[]')[0].replace('len(msg)<256','len(msg)<64')
env={'__file__':str(R/'evidence/joint-fixture11-20261026/JFm_generate.py')};exec(base,env)
files={};plan=[];tree=json.loads((P/'JGc_MERKLE_PREFLIGHT.json').read_text())['trees'][2]
# Each named certificate includes <=3 blocks for a leaf, <=2 for a parent.
groups=[list(range(i,min(i+2,12))) for i in range(0,12,2)]+[list(range(i,min(i+4,len(tree['hashes'])))) for i in range(12,len(tree['hashes']),4)]
for group in groups:
 module=f'JGc_TX2_M2H{group[0]:03}'
 out='import JFp_SHABlocks\nset_option autoImplicit false\n'
 for i in group:
  row=tree['hashes'][i];name=f'JGc_TX2_M2.Hash{i:03}';digest=env['cert'](name,bytes(row['message']));assert list(digest)==row['digest']
  text=env['files'][R/'lean'/(name+'.lean')];out+='\n'+text[text.index('namespace AspisR1.'):]
 files[R/'lean'/(module+'.lean')]=out
 plan.append(dict(module=module,hashes=group,blocks=sum(tree['hashes'][i]['blocks'] for i in group)))
assert max(r['blocks'] for r in plan)<=8
files[P/'JGc_HASH_PLAN.json']=json.dumps(plan,indent=2)+'\n'
for f,s in files.items():
 if '--check' in sys.argv:assert f.read_text()==s,f
 else:f.write_text(s)
print('preflight:',len(plan),'modules;',sum(x['blocks'] for x in plan),'blocks; max8; next consumer folded-tree authentication')
