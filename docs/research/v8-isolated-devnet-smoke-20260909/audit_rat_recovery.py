#!/usr/bin/env python3
import json,base64,time,hashlib
import devnet as d
from solders.pubkey import Pubkey
h=d.EVIDENCE
idl=json.loads((h/'rat-authoritative-idl.json').read_text())
def decode(typ,b):
 fields=next(t['type']['fields'] for t in idl['types'] if t['name']==typ);o=8
 def read(t):
  nonlocal o
  if isinstance(t,dict) and 'array' in t:return [read(t['array'][0]) for _ in range(t['array'][1])]
  if t=='pubkey':v=str(Pubkey.from_bytes(b[o:o+32]));o+=32;return v
  if t=='bool':assert b[o] in (0,1);v=bool(b[o]);o+=1;return v
  assert isinstance(t,str) and t[0] in 'ui';n=int(t[1:])//8;assert o+n<=len(b);v=int.from_bytes(b[o:o+n],'little',signed=t[0]=='i');o+=n;return v
 return {f['name']:read(f['type']) for f in fields}
if __name__=='__main__':
 assert d.rpc('getGenesisHash',[])==d.GENESIS
 raw=json.loads((h/'rat-devnet-account-rent.json').read_text());games=[a for a in raw if a['account']['space']==1024]
 r=d.rpc('getMultipleAccounts',[[a['pubkey'] for a in games],{'encoding':'base64','commitment':'finalized'}]);now=d.rpc('getBlockTime',[r['context']['slot']]);out=[]
 for a,b in zip(games,r['value']):
  
  try:s=decode('GameAccount',base64.b64decode(b['data'][0]))
  except Exception as e:
   out.append({'address':a['pubkey'],'decode_error':type(e).__name__});continue
  last=max(s[k] for k in ['created_at','turn_deadline','resolution_deadline','contribution_deadline','flag_reveal_deadline','discard_deadline']);out.append({'address':a['pubkey'],'state':s,'lamports':b['lamports'],'last_activity':last,'age_days':(now-last)/86400})
 d.save(h/'rat-recovery-games.json',{'slot':r['context']['slot'],'unix_time':now,'games':out});good=[g for g in out if 'state' in g];print({'games':len(out),'decoded':len(good),'oldest_days':max(g['age_days'] for g in good),'newest_days':min(g['age_days'] for g in good),'staked':sum(g['state']['staked_mode'] for g in good)})
