#!/usr/bin/env python3
"""Local ELF/warning audit; source embedded in output, no build or host tool."""
from pathlib import Path
import hashlib,json,re,resource,struct,sys,time,platform
START=time.monotonic(); W=Path(sys.argv[1]).resolve()

def sha(b):return hashlib.sha256(b).hexdigest()
def cstr(b,i):return b[i:b.index(b'\0',i)].decode('utf-8','replace')
def elf(path):
 b=path.read_bytes();h=struct.unpack_from('<16sHHIQQQIHHHHHH',b);assert h[0][:6]==b'\x7fELF\x02\x01';assert h[12]>0 and h[11]==64
 raw=[struct.unpack_from('<IIQQQQIIQQ',b,h[6]+i*h[11]) for i in range(h[12])];names=b[raw[h[13]][4]:raw[h[13]][4]+raw[h[13]][5]];sections=[]
 for i,s in enumerate(raw):sections.append({'index':i,'name':cstr(names,s[0]),'type':s[1],'flags':s[2],'address':s[3],'offset':s[4],'bytes':s[5],'link':s[6],'info':s[7],'entry_size':s[9]})
 tabs={};symbols=[]
 for s in sections:
  if s['type'] not in {2,11}:continue
  assert s['entry_size']==24
  strings=sections[s['link']];st=b[strings['offset']:strings['offset']+strings['bytes']];tab=[]
  for i in range(s['bytes']//24):
   n,info,other,index,address,size=struct.unpack_from('<IBBHQQ',b,s['offset']+i*24);q={'name':cstr(st,n),'type':info&15,'binding':info>>4,'section_index':index,'address':address,'bytes':size,'table':s['name']};tab.append(q);symbols.append(q)
  tabs[s['index']]=tab
 relocs=[]
 for s in sections:
  if s['type'] not in {4,9}:continue
  width=24 if s['type']==4 else 16;assert s['entry_size']==width
  for i in range(s['bytes']//width):
   values=struct.unpack_from('<QQq' if width==24 else'<QQ',b,s['offset']+i*width);offset,info=values[:2];idx=info>>32;tab=tabs[s['link']];assert idx<len(tab);relocs.append({'section':s['name'],'offset':offset,'type':info&0xffffffff,'symbol':tab[idx]['name'],'addend':values[2] if width==24 else None})
 functions=[s for s in symbols if s['type']==2 and s['section_index']!=0 and s['name']]
 if path.name=='linked.elf':assert any(s['name']=='.symtab' for s in sections)
 return {'path':str(path),'sha256':sha(b),'bytes':len(b),'machine':h[2],'entry':h[4],'sections':sections,'symbols':symbols,'functions':functions,'relocations':relocs,'raw':b}

linked=elf(W/'linked.elf');stripped=elf(W/'stripped.so');log=(W/'build.log').read_text();numeric=[];overwrites=[];unparsed=[]
for i,line in enumerate(log.splitlines(),1):
 m=re.search(r'Function (\S+) Stack offset of (\d+) exceeded max offset of (\d+) by (\d+) bytes,.*Estimated function frame size: (\d+) bytes',line)
 o=re.search(r'A function call in method (\S+) overwrites values in the frame',line)
 if m:
  name,offset,limit,excess,frame=m.groups();numeric.append({'line_number':i,'raw_line':line,'symbol':name,'offset':int(offset),'limit':int(limit),'excess':int(excess),'frame_size':int(frame)})
 elif o:overwrites.append({'line_number':i,'raw_line':line,'symbol':o[1]})
 elif re.match(r'(?:Error|error|Warning|warning):',line) and re.search(r'stack|frame|overwrit',line,re.I):unparsed.append({'line_number':i,'raw_line':line})
byname={}
for f in linked['functions']:byname.setdefault(f['name'],[]).append(f)
all_symbols={s['name'] for s in linked['symbols']};all_reloc_names={r['symbol'] for r in linked['relocations']}
for n in numeric:
 name=n['symbol'];n['linked_definitions']=byname.get(name,[]);n['linked_symbol_table_mentions']=name in all_symbols;n['relocation_mentions']=[r for r in linked['relocations'] if r['symbol']==name]
 aliases=[f for f in linked['functions'] if f['name'].startswith(name+'.') or name.startswith(f['name']+'.')]
 n['possible_renamed_aliases']=aliases
 if n['linked_definitions']:
  n['classification']='SURVIVING_OVERSIZED_FRAME';n['reason']='The exact compiler-warning mangled function has a defined function body in the complete unstripped linked ELF. No strip waiver applies.'
 elif aliases or n['linked_symbol_table_mentions'] or n['relocation_mentions']:
  n['classification']='REVIEW_REQUIRED';n['reason']='No exact defined body, but alias/symbol/relocation evidence requires explicit resolution; absence is not assumed.'
 else:
  assert name.startswith(('_ZN','_R'))
  n['classification']='UNREACHABLE_ABSENT_FROM_LINKED_ELF';n['reason']='Exact raw compiler-warning mangled name is absent from BOTH linked .symtab/.dynsym definitions/mentions and all linked relocation targets; no surviving program frame. Complete unstripped symbol inventory was checked, not merely stripped symbols. No graph reachability flag is inherited.'
for o in overwrites:
 o['linked_definitions']=byname.get(o['symbol'],[])
 o['linked_symbol_table_mentions']=o['symbol'] in all_symbols
 o['relocation_mentions']=[r for r in linked['relocations'] if r['symbol']==o['symbol']]
 o['possible_renamed_aliases']=[f for f in linked['functions'] if f['name'].startswith(o['symbol']+'.') or o['symbol'].startswith(f['name']+'.')]
 if o['linked_definitions']:
  o['classification']='SURVIVING_CALL_OVERWRITE_DIAGNOSTIC'
  o['reason']='The exact warned function body survives in the complete linked ELF; no strip or generic-source waiver.'
 elif o['possible_renamed_aliases'] or o['linked_symbol_table_mentions'] or o['relocation_mentions']:
  o['classification']='REVIEW_REQUIRED';o['reason']='Alias/symbol/relocation evidence requires explicit resolution.'
 else:
  assert o['symbol'].startswith(('_ZN','_R'))
  o['classification']='UNREACHABLE_ABSENT_FROM_LINKED_ELF'
  o['reason']='Exact warned mangled function absent from complete linked .symtab/.dynsym definitions/mentions and relocation targets; no surviving frame for this call-site diagnostic.'
actual=[]
for f in linked['functions']:
 if not any(n in f['name'] for n in ['verifier3tx1','verifier10tx1_finish','verifier11tx1_prepare']):continue
 section=linked['sections'][f['section_index']];start=section['offset']+f['address']-section['address'];code=linked['raw'][start:start+f['bytes']];assert len(code)==f['bytes'] and len(code)%8==0;stack_refs=[]
 for i in range(0,len(code),8):
  op,regs,offset,imm=struct.unpack_from('<BBhi',code,i);cl=op&7;dst=regs&15;src=regs>>4;base=src if cl==1 else dst
  if cl in {1,2,3} and base==10 and offset<0:stack_refs.append({'address':f['address']+i,'offset':offset,'opcode':op})
 actual.append({**f,'direct_fp_relative_memory_access_min_offset':min([s['offset'] for s in stack_refs],default=0),'direct_fp_relative_memory_accesses':stack_refs,'compiler_numeric_warnings':[n for n in numeric if n['symbol']==f['name']],'overwrite_diagnostics':[o for o in overwrites if o['symbol']==f['name']],'measurement_scope':'Direct r10 memory operands only; not a complete alias/liveness analysis. Compiler warnings provide reported frame values; absence of warning is a <=4096 bound under the complete compiler diagnostic inventory, not a fabricated exact frame.'})
assert any('verifier3tx1' in f['name'] for f in actual);assert any('verifier10tx1_finish' in f['name'] for f in actual);assert any('verifier11tx1_prepare' in f['name'] for f in actual)
exec_sections=[]
for s in linked['sections']:
 if not s['flags']&4:continue
 matches=[q for q in stripped['sections'] if q['name']==s['name'] and q['flags']&4];assert len(matches)==1;q=matches[0];a=linked['raw'][s['offset']:s['offset']+s['bytes']];b=stripped['raw'][q['offset']:q['offset']+q['bytes']];assert a==b and s['address']==q['address'];exec_sections.append({'name':s['name'],'address':s['address'],'bytes':s['bytes'],'sha256':sha(a),'linked_stripped_byte_identical':True})
# Decode direct SBPF call-immediate edges; use explicit witness paths only.
# This is not a claim that unresolved indirect calls are closed by this graph.
addresses={f['address']:f['name'] for f in linked['functions']}
call_edges=[]
for f in linked['functions']:
 section=linked['sections'][f['section_index']];start=section['offset']+f['address']-section['address'];code=linked['raw'][start:start+f['bytes']]
 for i in range(0,len(code)-7,8):
  op,regs,offset,imm=struct.unpack_from('<BBhi',code,i)
  if op==0x85:
   pc=f['address']+i;target=pc+8+8*imm
   if target in addresses:call_edges.append({'caller':f['name'],'instruction_address':pc,'immediate':imm,'target_address':target,'callee':addresses[target]})
entry_names=[f['name'] for f in linked['functions'] if f['name']=='entrypoint' or f['address']==linked['entry']]
def path_to(fragment):
 from collections import deque
 q=deque((n,[]) for n in entry_names);seen=set()
 while q:
  n,path=q.popleft()
  if n in seen:continue
  seen.add(n)
  if fragment in n:return {'root':path[0]['caller'] if path else n,'target':n,'direct_call_path':path}
  for edge in call_edges:
   if edge['caller']==n:q.append((edge['callee'],path+[edge]))
 return None
source_paths={name:path_to(fragment) for name,fragment in [('stage1','r1_pool_adapter6stage1'),('stage2','r1_pool_adapter6stage2'),('actual_tx1','verifier3tx1'),('actual_tx1_finish','verifier10tx1_finish'),('actual_tx1_prepare','verifier11tx1_prepare')]}

survivors=[n for n in numeric if n['classification']!='UNREACHABLE_ABSENT_FROM_LINKED_ELF']
surviving_overwrites=[o for o in overwrites if o['classification']!='UNREACHABLE_ABSENT_FROM_LINKED_ELF']
report={'gate_pass':not(survivors or surviving_overwrites or unparsed),'linked_sha256':linked['sha256'],'stripped_sha256':stripped['sha256'],'numeric_diagnostics':numeric,'overwrite_diagnostics':overwrites,'unparsed':unparsed,'actual_tx1':actual,'call_paths':source_paths,'all_direct_call_edges':call_edges,'surviving_oversized':survivors,'surviving_overwrites':surviving_overwrites,'policy':'Every surviving oversized frame fails conservatively; exact absence from full linked ELF, symbols and relocations required for waiver.'}
(W/'stack-audit.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps({k:report[k] for k in ['gate_pass','linked_sha256','stripped_sha256','surviving_oversized','surviving_overwrites','unparsed']}));assert report['gate_pass']
