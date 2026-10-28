from pathlib import Path
import json,struct,hashlib,subprocess,bisect,re
H=Path('/home/dombarker/project-offloads/codex-cx-native-sbfstack-20261028')
def elf(p):
 b=Path(p).read_bytes();off=struct.unpack_from('<Q',b,40)[0];ent,n,idx=struct.unpack_from('<HHH',b,58)
 ss=[struct.unpack_from('<IIQQQQIIQQ',b,off+i*ent) for i in range(n)];names=b[ss[idx][4]:ss[idx][4]+ss[idx][5]]
 sections={names[s[0]:].split(b'\0')[0].decode():{'addr':s[3],'bytes':b[s[4]:s[4]+s[5]],'header':s} for s in ss}
 syms=[]
 for sec in sections.values():
  s=sec['header']
  if s[1] not in [2,11]:continue
  st=ss[s[6]];strings=b[st[4]:st[4]+st[5]]
  for at in range(s[4],s[4]+s[5],s[9]):
   nm,info,other,shndx,val,size=struct.unpack_from('<IBBHQQ',b,at)
   if info&15==2 and shndx:syms.append({'symbol':strings[nm:].split(b'\0')[0].decode(),'addr':val,'size':size})
 return b,sections,syms
warnings=json.loads((H/'NDC_WARNINGS.json').read_text());u=json.loads((H/'NDC_UNSTRIPPED.json').read_text());out={}
for mode,a in json.loads((H/'NDC_ELFS.json').read_text()).items():
 b,s,dyn=elf(a['path']);ub,us,syms=elf(u['pool' if mode=='pool' else 'verifier']['path']);text=s['.text']['bytes'];base=s['.text']['addr']
 funcs=sorted({x['addr']:x for x in syms}.values(),key=lambda x:x['addr']);starts=[f['addr'] for f in funcs]
 def owner(addr):
  i=bisect.bisect_right(starts,addr)-1
  return funcs[i] if i>=0 and addr<funcs[i]['addr']+funcs[i]['size'] else None
 edges={f['addr']:set() for f in funcs};ind=[];bad=[]
 for at in range(0,len(text),8):
  op,regs,offset,imm=struct.unpack_from('<BBhi',text,at)
  if op==0x85 and regs>>4==1:
   src=owner(base+at);target=base+at+8+imm*8
   if src:
    edges[src['addr']].add(target)
    if target not in starts:bad.append({'pc':base+at,'target':target})
  if op==0x8d:ind.append({'pc':base+at,'owner':owner(base+at)})
 entry=struct.unpack_from('<Q',b,24)[0];seen=set();todo=[entry]
 while todo:
  f=todo.pop()
  if f in seen:continue
  seen.add(f);todo.extend(edges.get(f,[]))
 matches=[]
 for w in warnings:
  found=[f for f in funcs if re.sub(r'17h[0-9a-f]{16}E$','',f['symbol'])==w['identity']]
  matches.append({'identity':w['identity'],'matches':found,'entry_direct_reachable':[f['addr'] in seen for f in found]})
 diffs=[i for i,(x,y) in enumerate(zip(text,us['.text']['bytes'])) if x!=y]
 out[mode]={'elf':a,'unstripped':u['pool' if mode=='pool' else 'verifier'],'text_sha256':hashlib.sha256(text).hexdigest(),'unstripped_text_sha256':hashlib.sha256(us['.text']['bytes']).hexdigest(),'text_equal':text==us['.text']['bytes'],'text_diff_bytes':len(diffs),'text_diff_owners':list({owner(base+i)['symbol'] if owner(base+i) else '?' for i in diffs}),'entry':entry,'function_count':len(funcs),'direct_reachable_count':len(seen),'unresolved_direct':bad,'indirect_calls':ind,'warnings':matches}
 (H/('NDC_'+mode+'_callgraph.json')).write_text(json.dumps({'functions':funcs,'edges':{str(k):sorted(v) for k,v in edges.items()},'entry_reachable':sorted(seen)},indent=2)+'\n')
 print(mode,'equal',out[mode]['text_equal'],'diffbytes',len(diffs),'diffowners',out[mode]['text_diff_owners'],'functions',len(funcs),'reachable',len(seen),'indirect',len(ind),'bad',len(bad))
 print('PRESENT',json.dumps([m for m in matches if m['matches']]))
(H/'NDC_LINKAGE.json').write_text(json.dumps(out,indent=2)+'\n')
