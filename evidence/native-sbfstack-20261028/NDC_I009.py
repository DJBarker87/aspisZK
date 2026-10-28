from pathlib import Path
import struct,subprocess,json,hashlib,re,shutil,bisect
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
result={}
for mode,a in json.loads((H/'NDC_ELFS.json').read_text()).items():
 b,s,dy=elf(a['path']);g=json.loads((H/('NDC_'+mode+'_callgraph.json')).read_text());fn={f['addr']:f for f in g['functions']};base=s['.text']['addr'];t=s['.text']['bytes'];strtab=s['.dynstr']['bytes'];syms=[]
 for at in range(0,len(s['.dynsym']['bytes']),24):
  nm,info,other,idx,val,size=struct.unpack_from('<IBBHQQ',s['.dynsym']['bytes'],at);syms.append({'name':strtab[nm:].split(b'\0')[0].decode(),'value':val})
 rels={}
 for at in range(0,len(s['.rel.dyn']['bytes']),16):
  off,info=struct.unpack_from('<QQ',s['.rel.dyn']['bytes'],at)
  if info&0xffffffff==10:rels[off]=syms[info>>32]
 edges={k:[] for k in fn};relcalls=[];unknown=[];stack={}
 for addr,f in fn.items():
  maxneg=0
  for pc in range(addr,addr+f['size'],8):
   op,regs,off,imm=struct.unpack_from('<BBhi',t,pc-base)
   if op==0x85 and regs>>4==1:
    if pc in rels:
     relcalls.append({'pc':pc,'caller':f['symbol'],'symbol':rels[pc]})
     target=rels[pc]['value']
     if target in fn:edges[addr].append(target)
    else:
     target=pc+8+imm*8
     if target in fn:edges[addr].append(target)
     else:unknown.append({'pc':pc,'target':target})
   # Count only actual direct r10 memory operands; excludes arbitrary indirect-derived addresses.
   if ((op&7)==1 and regs>>4==10) or ((op&7) in [2,3] and regs&15==10):maxneg=max(maxneg,-off)
  stack[f['symbol']]=maxneg
 seen=set();todo=[struct.unpack_from('<Q',b,24)[0]]
 while todo:
  f=todo.pop()
  if f in seen:continue
  seen.add(f);todo.extend(edges.get(f,[]))
 result[mode]={'e_flags':struct.unpack_from('<I',b,48)[0],'entry':struct.unpack_from('<Q',b,24)[0],'relocated_calls':relcalls,'unresolved_direct':unknown,'direct_reachable_functions':[fn[v] for v in sorted(seen)],'indirect_call_count':len(json.loads((H/'NDC_LINKAGE.json').read_text())[mode]['indirect_calls']),'edges':{str(k):sorted(set(v)) for k,v in edges.items()},'direct_r10_max_negative_offsets':stack}
 print('GRAPH',mode,'flags',result[mode]['e_flags'],'direct',len(seen),'unresolved',len(unknown),'relocated',len(relcalls),'max_direct_r10',max(stack.values()))
(H/'NDC_CALLGRAPH_FINAL.json').write_text(json.dumps(result,indent=2)+'\n')
# Exact native build feature fingerprints and tools, without another compilation.
features={}
for p in (H/'NDC_target_native/release/.fingerprint').glob('aspis-*/lib-*.json'):
 j=json.loads(p.read_text());features[str(p.relative_to(H))]={'features':j.get('features'),'declared_features':j.get('declared_features'),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()}
(H/'NDC_NATIVE_FEATURES.json').write_text(json.dumps(features,indent=2)+'\n')
tools={}
for cmd in [['/home/dombarker/.cargo/bin/rustc','-vV'],['/home/dombarker/.cargo/bin/cargo','-V'],['/home/dombarker/.cache/solana/v1.52/platform-tools/llvm/bin/llvm-objdump','--version'],['/usr/bin/nm','--version']]:
 q=subprocess.run(cmd,capture_output=True,text=True);tools[cmd[0]]={'command':cmd,'exit':q.returncode,'stdout':q.stdout,'stderr':q.stderr,'sha256':hashlib.sha256(Path(cmd[0]).read_bytes()).hexdigest()}
(H/'NDC_TOOLS.json').write_text(json.dumps(tools,indent=2)+'\n')
# Retain useful emitted native generic headers and source checks before deleting own rebuildable target.
generic={}
for p in (H/'NDC_target_native/release/deps').glob('aspis_core*.ll'):
 ls=p.read_text().splitlines();generic[p.name]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size,'headers':[{'line':i+1,'text':l} for i,l in enumerate(ls) if l.startswith('define ') and ('EncodingDomain6encode' in l or 'try_from_fn' in l or 'extend_trusted' in l)]}
(H/'NDC_NATIVE_GENERIC_HEADERS.json').write_text(json.dumps(generic,indent=2)+'\n')
cg=Path('/sys/fs/cgroup')/Path('/proc/self/cgroup').read_text().split('0::',1)[1].strip().lstrip('/')
r={'limits':{n:(cg/n).read_text().strip() for n in ['memory.high','memory.max','memory.swap.max','pids.max','memory.peak','memory.swap.peak']},'removed_only':str(H/'NDC_target_native'),'cache_note':'No Lean work; named own Lean cache never created or removed. No imported Lean objects.'}
assert (H/'NDC_target_native').is_dir() and not (H/'NDC_target_native').is_symlink();shutil.rmtree(H/'NDC_target_native')
(H/'NDC_CLEANUP.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
