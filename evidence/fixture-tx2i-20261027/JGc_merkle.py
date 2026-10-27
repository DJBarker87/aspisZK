"""Read-only numerical preflight of the retained batch1; no proof credit."""
from pathlib import Path
import re,json,hashlib
P=Path(__file__).resolve().parent;R=P.parents[1]
def raw_files(glob):
 out=[]
 for f in sorted((R/'lean').glob(glob)):
  for line in f.read_text().splitlines():
   if line.startswith('def c'):
    if 'replicate' in line:
     n,v=map(int,re.search(r'replicate (\d+) (\d+)#u8',line).groups());out.extend([v]*n)
    else:out.extend(map(int,re.findall(r'(\d+)#u8',line)))
 return bytes(out)
raw=raw_files('JFx_DataProof*.lean');cp=raw_files('JFx_DataCheckpoint*.lean')
assert len(raw)==57607 and hashlib.sha256(raw).hexdigest()=='55386c507d3feeebfc45272a1cf15c33ccb9ccf0a8a8f41180fc654d806fff6f'
assert len(cp)==1768
queries=[132355,218094,178080,149624,166165,42158,179622,21248,63860,55377,185637,14297]
capacity=[146,146,128,172,172,150]
rows=[]
for tree in range(3):
 slot=3+tree;start=28359+32*sum(capacity[:slot]);nodes=[raw[start+32*i:start+32*(i+1)] for i in range(capacity[slot])]
 leaves=[];hashes=[]
 for i,q in enumerate(queries):
  pos=10+i;o=raw[10055+832*pos:10055+832*(pos+1)]
  if tree==0:msg=bytes([16,113])+o[:480]+o[608:640]
  elif tree==1:msg=bytes([16,241])+o[480:608]+o[640:672]
  else:msg=bytes([16,114])+o[672:800]+o[800:832]
  digest=hashlib.sha256(msg).digest();index=q//4 if tree==2 else q
  leaves.append((index,digest));hashes.append(dict(kind='leaf',position=pos,index=index,message=list(msg),digest=list(digest),blocks=(len(msg)+9+63)//64))
 frontier=dict(sorted(leaves));cursor=0
 for level in range(18):
  after={};keys=sorted(frontier);j=0
  while j<len(keys):
   index=keys[j];v=frontier[index]
   if index%2==0 and j+1<len(keys) and keys[j+1]==index+1:left,right=v,frontier[index+1];j+=2;source='occupied'
   elif index%2==0:left,right=v,nodes[cursor];cursor+=1;j+=1;source='sibling-right'
   else:left,right=nodes[cursor],v;cursor+=1;j+=1;source='sibling-left'
   msg=bytes([18])+left+right;digest=hashlib.sha256(msg).digest()
   hashes.append(dict(kind='parent',level=level,index=index//2,source=source,cursor=cursor,message=list(msg),digest=list(digest),blocks=2))
   after[index//2]=digest
  frontier=after
 assert list(frontier)==[0]
 assert all(x==bytes(32) for x in nodes[cursor:]),(tree,cursor,len(nodes))
 root=frontier[0]
 expected=cp[112+32*tree:144+32*tree] if tree<2 else raw[7751:7783]
 rows.append(dict(tree=tree,slot=slot,slot_start=start,consumed=cursor,root=root.hex(),expected=expected.hex(),root_matches=root==expected,hashes=hashes,blocks=sum(x['blocks'] for x in hashes)))
out=dict(classification='numerical preflight only; hashlib is not a Lean theorem',trees=rows,total_blocks=sum(r['blocks'] for r in rows),max_blocks_per_certificate_module=8)
(P/'JGc_MERKLE_PREFLIGHT.json').write_text(json.dumps(out,indent=2)+'\n')
print([(r['tree'],r['root_matches'],len(r['hashes']),r['blocks'],r['root']) for r in rows]);print('total compression blocks',out['total_blocks'])
