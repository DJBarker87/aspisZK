#!/usr/bin/env python3
"""Read-only frozen ELF/LLBC census; output is audit data, never a closure claim."""
import collections,hashlib,json,re,struct,subprocess
from pathlib import Path
H=Path('/home/dombarker/project-offloads/codex-cx-s10-inventory-20261021')
F=Path('/home/dombarker/project-offloads/codex-cx-pin-20261020')
NM=Path('/home/dombarker/.cache/solana/v1.52/platform-tools/rust/lib/rustlib/x86_64-unknown-linux-gnu/bin/llvm-nm')
sha=lambda b:hashlib.sha256(b).hexdigest()
def dump(p,x): p.write_text(json.dumps(x,indent=2,sort_keys=True)+'\n')
def elf(raw):
 assert raw[:6]==b'\x7fELF\x02\x01'
 h=struct.unpack_from('<16sHHIQQQIHHHHHH',raw)
 sections=[struct.unpack_from('<IIQQQQIIQQ',raw,h[6]+i*h[11]) for i in range(h[12])]
 names=sections[h[13]]; strings=raw[names[4]:names[4]+names[5]]
 def name(i):return strings[i:strings.index(b'\0',i)].decode()
 return {name(s[0]):s for s in sections}
result={}
for mode,pin in [('default','dfc2a91ab24e1ec4f57debd8f124cb4f6a3c38ba2662b7318e2e4f3b4acdde34'),('devnet','fb2fc048f6499a4775051d0267c76e8ca273b28f557bfd3b5fb65b2f687c8b78'),('pool','121f3e29741f510e6dc42d0345fc3c36217600f0be337094855c4a9da2581548')]:
 d=F/'artifacts'/mode; deployed=d/('aspis_pool.so' if mode=='pool' else 'aspis_r1_cost_probe_program.so'); linked=d/'linked.elf'
 raw=linked.read_bytes();dep=deployed.read_bytes();assert sha(dep)==pin
 sections=elf(raw);ds=elf(dep);t=sections['.text'];dt=ds['.text'];text=raw[t[4]:t[4]+t[5]]
 assert text==dep[dt[4]:dt[4]+dt[5]]
 output=subprocess.check_output([str(NM),'--defined-only','--numeric-sort','--print-size','--demangle',str(linked)],text=True)
 symbols=[]
 for line in output.splitlines():
  m=re.fullmatch(r'([0-9a-f]+) ([0-9a-f]+) ([tT]) (.+)',line)
  if m:symbols.append(dict(address=int(m[1],16),size=int(m[2],16),name=m[4]))
 byaddr={s['address']:s for s in symbols};relocs={}
 rs=sections['.rel.dyn'];sy=sections['.dynsym'];st=sections['.dynstr'];string=raw[st[4]:st[4]+st[5]]
 for pos in range(rs[4],rs[4]+rs[5],16):
  addr,info=struct.unpack_from('<QQ',raw,pos);idx=info>>32
  n=struct.unpack_from('<I',raw,sy[4]+24*idx)[0]
  relocs[addr]=dict(kind=info&0xffffffff,symbol=string[n:string.index(b'\0',n)].decode())
 calls=[]
 for s in symbols:
  for addr in range(s['address'],s['address']+s['size'],8):
   pos=t[4]+addr-t[3];code,regs,off,imm=struct.unpack_from('<BBhi',raw,pos)
   if code not in (0x85,0x8d):continue
   c=dict(caller=s['address'],address=addr,opcode=code,registers=regs,immediate=imm)
   if code==0x8d:c['kind']='indirect';c['target']=None
   elif addr in relocs and relocs[addr]['symbol']:
    c.update(kind='syscall',target=relocs[addr]['symbol'],relocation=relocs[addr])
   elif regs>>4==1:
    dest=addr+8+8*imm;c.update(kind='direct',target=dest,resolved=dest in byaddr)
   else:c.update(kind='unresolved',target=None)
   calls.append(c)
 # Direct graph is a lower bound; callx prevents asserting full reachability.
 roots=[s['address'] for s in symbols if s['name']=='entrypoint'];seen=set(roots);todo=list(roots)
 edges=collections.defaultdict(list)
 for c in calls:edges[c['caller']].append(c)
 while todo:
  for c in edges[todo.pop()]:
   if c['kind']=='direct' and c['target'] in byaddr and c['target'] not in seen:seen.add(c['target']);todo.append(c['target'])
 result[mode]=dict(deployed=dict(path=str(deployed),sha256=pin,bytes=len(dep)),linked=dict(path=str(linked),sha256=sha(raw),bytes=len(raw)),text_sha256=sha(text),text_equal=True,symbols=symbols,calls=calls,roots=roots,direct_reachable=sorted(seen),indirect_calls=sum(c['kind']=='indirect' for c in calls),unresolved_calls=sum(c['kind']=='unresolved' or c.get('resolved') is False for c in calls),scope='All linked text symbols plus direct-entrypoint lower bound; inlined declarations and indirect targets NOT recovered')
 assert roots
out=H/'collected';out.mkdir(exist_ok=True)
dump(out/'elf-graphs.json',dict(schema='s10-frozen-elf-graphs-v1',tools={str(NM):sha(NM.read_bytes())},artifacts=result))
llbc=F/'extraction-freeze/Stage2.llbc';raw=llbc.read_bytes();assert sha(raw)=='f11e40b4119578eee1ebef90874f436dc35b1076f6db27baaa92a79c0919538d'
x=json.loads(raw);t=x['translated'];rows=[]
def walk(v,path=()):
 if isinstance(v,dict):
  yield path,v
  for k,z in v.items():yield from walk(z,path+(k,))
 elif isinstance(v,list):
  for i,z in enumerate(v):yield from walk(z,path+(i,))
for f in t['fun_decls']:
 if f is None:continue
 m=f['item_meta'];name='::'.join(n['Ident'][0] if 'Ident' in n else json.dumps(n,sort_keys=True) for n in m['name'])
 span=m['span']['data'];file=t['files'][span['file_id']]
 calls=[];refs=[]
 for path,v in walk(f['body']):
  if 'Call' in v:
   call=v['Call']['call'];func=call['func'];reg=func.get('Regular',{});kind=reg.get('kind',{});fun=kind.get('Fun',{})
   calls.append(dict(path=list(path),function=func,target=fun.get('Regular'),kind='direct' if 'Regular' in fun else 'builtin' if 'Builtin' in fun else 'indirect_or_trait'))
  if 'FnPtr' in v:refs.append(dict(path=list(path),value=v['FnPtr']))
 rows.append(dict(id=f['def_id'],name=name,name_ast=m['name'],span=span,file=file['name'],source_text_sha256=sha((m['source_text'] or '').encode()),opacity=m['opacity'],body_kind='Opaque' if f['body']=='Opaque' else 'Structured',generics=f['generics'],calls=calls,function_pointer_mentions=refs))
byid={f['id']:f for f in rows};seen={0};todo=[0]
while todo:
 for c in byid[todo.pop()]['calls']:
  target=c['target']
  if target is not None and target not in seen:assert target in byid;seen.add(target);todo.append(target)
dump(out/'stage2-llbc.json',dict(schema='s10-llbc-call-census-v1',input=dict(path=str(llbc),sha256=sha(raw),bytes=len(raw),has_errors=x['has_errors'],charon_version=x['charon_version']),options=t['options'],declarations=rows,direct_reachable=sorted(seen),scope='Generic retained Stage2 cut; no entrypoint, no instantiated H, opaque backends explicit; not full reachability'))
print(json.dumps({mode:dict(symbols=len(v['symbols']),calls=len(v['calls']),direct_reachable=len(v['direct_reachable']),indirect=v['indirect_calls'],unresolved=v['unresolved_calls']) for mode,v in result.items()}),flush=True)
