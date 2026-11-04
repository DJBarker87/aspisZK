"""Conservative direct-call/branch reachability for the pinned SDK interval."""
from pathlib import Path
import re,lzma,json,hashlib
E=Path(__file__).resolve().parent
def decode(text):
 ins={}
 for line in text.splitlines():
  m=re.match(r'\s*([0-9a-f]+):\s+((?:[0-9a-f]{2}\s+)+)\t(.+)',line)
  if m:ins[int(m[1],16)]=(bytes.fromhex(m[2]),m[3].strip())
 return ins
raw=lzma.decompress((E/'NFO_pool_disassembly.txt.xz').read_bytes());assert hashlib.sha256(raw).hexdigest()==(E/'NFO_pool_disassembly.txt.sha256').read_text().strip()
ins=decode(raw.decode());rel={int(m[1],16):m[2] for l in (E/'NFO_pool_relocations.txt').read_text().splitlines() if (m:=re.match(r'([0-9a-f]+) R_SBF_64_32\s+(\S+)',l))}
def reachable(start,stop):
 pending=[start];seen=set();calls=[];syscalls=[];unknown=[];stops=[]
 while pending:
  a=pending.pop()
  if a in seen:continue
  seen.add(a)
  if a in stop:stops.append(hex(a));continue
  if a not in ins:unknown.append(dict(address=hex(a),reason='missing instruction'));continue
  code,asm=ins[a];op=code[0];nxt=a+len(code)
  if op==0x95:continue
  if op==0x8d:unknown.append(dict(address=hex(a),reason='indirect call'));continue
  if op==0x85:
   if a in rel:syscalls.append(dict(address=hex(a),symbol=rel[a]))
   else:
    dest=a+8+int.from_bytes(code[4:8],'little',signed=True)*8
    calls.append(dict(address=hex(a),target=hex(dest)));pending.append(dest)
   pending.append(nxt);continue
  if (op&7) in [5,6]:
   dest=a+8+int.from_bytes(code[2:4],'little',signed=True)*8
   pending.append(dest)
   if op!=0x05 and a!=0x60f60:pending.append(nxt)
  else:pending.append(nxt)
 return dict(start=hex(start),stop_addresses=list(map(hex,stop)),visited=len(seen),internal_calls=calls,syscalls=syscalls,unresolved=unknown,reached_stops=stops)
rows=[reachable(0x60f60,[]),reachable(0x61028,[0x610a0])]
(E/'NFO_ELF_FLOW_ATTEMPT.json').write_text(json.dumps(rows,indent=1)+'\n')
assert all(not r['unresolved'] for r in rows),[(r['start'],r['unresolved']) for r in rows]
assert not any(s['symbol'] in ['sol_set_return_data','sol_invoke_signed_rust','sol_invoke_signed_c'] for r in rows for s in r['syscalls']),rows
assert rows[1]['reached_stops']==['0x610a0']
# The detector must reject planted syscall changes in either interval.
controls=[]
for a,symbol in [(0x60fd0,'sol_set_return_data'),(0x61058,'sol_invoke_signed_rust')]:
 old=rel.get(a);rel[a]=symbol
 r=reachable(rows[0]['start'] and 0x60f60 if a==0x60fd0 else 0x61028,[] if a==0x60fd0 else [0x610a0])
 controls.append(dict(address=hex(a),symbol=symbol,detected=any(s['symbol']==symbol for s in r['syscalls'])))
 if old is None:del rel[a]
 else:rel[a]=old
assert all(r['detected'] for r in controls)
(E/'NFO_ELF_FLOW.json').write_text(json.dumps(dict(status='PASS',method='static direct-call CFG; all branches except syscall-success r0=0 at 0x60f60; return approximation; excludes syscall body semantics',rows=rows,mutation_controls=controls),indent=1)+'\n')
print('PASS no intervening CPI/set in SDK post-invoke return or get initialization; 2 mutation controls')
