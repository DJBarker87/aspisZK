"""Per-body instruction alignment and diagnostic DWARF guide, never a proof."""
from pathlib import Path
import json,lzma,re,subprocess,sys,hashlib,difflib
D=Path(__file__).resolve().parent
L=D.parent/'codex-pv-l3a-20261029'
def run(n,kind,index):
 instances=json.loads((L/'instances.json').read_text())
 inv=[r for row in json.loads((L/'inversions.json').read_text()) for r in row['transfers']]
 row=instances[index] if kind=='body' else inv[index]
 addr=row['address'] if kind=='body' else row['caller']
 with lzma.open(L/'function-index.json.xz','rt') as f: funcs=json.load(f)
 if isinstance(funcs,dict):funcs=list(funcs.values())
 old=next(x for x in funcs if x['address']==addr)
 with lzma.open(L/'disassembly.txt.xz','rt') as f: source_asm=f.read()
 old['instructions']=[]
 for s in source_asm.splitlines():
  m=re.match(r'\s*([\da-f]+):\s+([a-z][a-z\d_.]*)\s*(.*)',s)
  if m and int(old['address'],16)<=int(m[1],16)<int(old['end'],16):
   old['instructions'].append(dict(address=hex(int(m[1],16)),op=m[2],args=m[3],text=s.strip()))
 symbols=json.loads((D/'symbol-address-comparison.json').read_text())
 same=[x for x in symbols if x['name'] in old['names']]
 assert len(same)==1 and len(same[0]['debug'])==1,same
 da,sz=same[0]['debug'][0]
 binary=D/'client-target/release/devnet_spend'
 asm=subprocess.check_output(['objdump','-d','-C','--no-show-raw-insn',f'--start-address={da}',f'--stop-address={da+sz}',str(binary)],text=True)
 debug=[]
 for s in asm.splitlines():
  m=re.match(r'\s*([\da-f]+):\s+([a-z][a-z\d_.]*)\s*(.*)',s)
  if m:debug.append(dict(address=hex(int(m[1],16)),op=m[2],args=m[3],text=s.strip()))
 def norm(i):
  s=i['args']
  # Alignment heuristic only: masks relocation/address operands, never data immediates.
  s=re.sub(r'-?0x[\da-f]+\(%rip\)', 'RIP_RELOC',s)
  s=re.sub(r'#.*','',s)
  if i['op'].startswith(('j','call')):s=re.sub(r'^[\da-f]+\s+<.*?>', 'DIRECT_TARGET',s)
  s=re.sub(r'<.*>', '',s)
  return i['op']+' '+s.strip()
 a=old['instructions'];na=[norm(i) for i in a];nb=[norm(i) for i in debug]
 sm=difflib.SequenceMatcher(None,na,nb,autojunk=False)
 pairs={ai+k:bi+k for ai,bi,c in sm.get_matching_blocks() for k in range(c)}
 changes=[dict(tag=t,baseline=[x,y],debug=[u,v],baseline_instructions=a[x:y],debug_instructions=debug[u:v]) for t,x,y,u,v in sm.get_opcodes() if t!='equal']
 with lzma.open(D/'dwarf-all-instances.json.xz','rt') as f: dies=json.load(f)
 overlapping=[x for x in dies if any(lo<da+sz and hi>da for lo,hi in x['ranges'])]
 # addr2line runs against DEBUG addresses exclusively.
 addresses=[x['address'] for x in debug]
 lines=subprocess.check_output(['addr2line','-a','-f','-i','-C','-e',str(binary),*addresses],text=True)
 (D/f'{n}-debug-lines.txt').write_text(lines)
 (D/f'{n}-debug-disassembly.txt').write_text(asm)
 (D/f'{n}-baseline-disassembly.txt').write_text('\n'.join(x['text'] for x in a)+'\n')
 result=dict(kind=kind,index=index,baseline=row,baseline_function={k:v for k,v in old.items() if k!='instructions'},debug_range=[hex(da),hex(da+sz)],baseline_instruction_count=len(a),debug_instruction_count=len(debug),aligned_instructions=len(pairs),masked_sequence_equal=na==nb,alignment_warning='Heuristic sequence alignment masks relocation operands; does not establish byte identity or preservation. DWARF is a guide ONLY.',changes=changes,diagnostic_inline_instances=overlapping)
 if kind=='call':
  site=int(row['site'],16);oi=next(i for i,x in enumerate(a) if int(x['address'],16)==site)
  result['baseline_call_context']=a[max(0,oi-35):oi+12]
  di=pairs.get(oi);result['debug_corresponding_site']=debug[di] if di is not None else None
 (D/f'{n}-detail.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(dict(kind=kind,index=index,baseline=addr,debug=hex(da),aligned=len(pairs),instructions=len(a),equal=na==nb,changes=len(changes),dies=len(overlapping))))
