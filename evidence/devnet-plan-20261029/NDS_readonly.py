#!/usr/bin/env python3
"""Allowlisted unsigned devnet reads; no wallet loading or transaction paths."""
import base64, datetime, json, pathlib, subprocess, urllib.request, time
O=pathlib.Path(__file__).resolve().parent
assert not (O/'NDS_RPC.json').exists(), 'retain previous receipts'
rows=[]
def rpc(method,params):
 assert method in {'getAccountInfo','getBalance','getVersion','getMinimumBalanceForRentExemption'}
 q={'jsonrpc':'2.0','id':len(rows)+1,'method':method,'params':params}
 row={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'request':q};rows.append(row)
 try:
  with urllib.request.urlopen(urllib.request.Request('https://api.devnet.solana.com',data=json.dumps(q).encode(),headers={'Content-Type':'application/json'}),timeout=25) as r: row['response']=json.load(r)
 except Exception as e:row['error']=str(e)
 (O/'NDS_RPC.json').write_text(json.dumps(rows,indent=2)+'\n');time.sleep(.8)
 return row.get('response',{}).get('result')
rpc('getVersion',[])
rpc('getBalance',['Xjb7roDVPDSPoZpUmDVUW5SMx21x7oQEg16dhb5TDXD',{'commitment':'finalized'}])
for n in [1563728+37,1563728+45,36]:rpc('getMinimumBalanceForRentExemption',[n,{'commitment':'finalized'}])
summary={}
for role,key in {'registry':'FUHo4ZRK5Q8TGkaMvUZhwyjXmCGz8qSR6hG19XwTycBr','entry':'EN4AqiZ7N571XtMRvoa7dFyuRsz7y3Ef3oD3doB7nFtW','master':'8YRunNHbLqBUzeZYh7VK6jsJDUup4jA1qTcKvPy4i2Lf'}.items():
 a=rpc('getAccountInfo',[key,{'commitment':'finalized','encoding':'base64'}])
 if not a or not a['value']:summary[role]={'available':False};continue
 b=base64.b64decode(a['value']['data'][0]);s={'address':key,'owner':a['value']['owner'],'context':a['context'],'bytes':len(b),'magic':b[:4].decode(errors='replace')}
 if role=='registry':s.update(version=b[4],flags=b[5],immutable=bool(b[5]&2),authority_zero=not any(b[40:72]),generation=int.from_bytes(b[104:112],'little'),pool_hex=b[8:40].hex())
 if role=='entry':s.update(verifier_hex=b[40:72].hex())
 summary[role]=s
(O/'NDS_STATE.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({'rpc_reads':len(rows),'state':summary,'balance':rows[1].get('response'),'rent':[x.get('response') for x in rows[2:5]]},indent=2))
