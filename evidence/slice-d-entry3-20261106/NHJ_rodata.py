"""Read-only named-symbol / loaded-image association; no compiler build or key access."""
from pathlib import Path
import struct,json,hashlib,re
B=Path(__file__).resolve().parent
F=Path('/home/dombarker/project-offloads/codex-cx-lowering2-20261026')
paths=dict(cache=F/'sbf-target-verifier/sbpf-solana-solana/release/aspis_r1_cost_probe_program.so',default=Path('/home/dombarker/project-offloads/codex-cx-native-elfscope-20261028/NCR_B003/artifacts/aspis_r1_cost_probe_program.so'),devnet=F/'build-devnet-v1/artifacts/aspis_r1_cost_probe_program.so')
expected=dict(default='f8c0ec72621fd5029a97d796c4a3623d0dc44a8e7074122372f9872915d143d4',devnet='63ad3e9cc096dcbb55b3ca7ac7c8e89e6a845796ab5e4f5b7d15db96f3784299')
sha=lambda b:hashlib.sha256(b).hexdigest()
def parse(path):
 b=path.read_bytes();assert b[:6]==b'\x7fELF\x02\x01'
 shoff=struct.unpack_from('<Q',b,40)[0];ents,n,si=struct.unpack_from('<HHH',b,58)
 raw=[struct.unpack_from('<IIQQQQIIQQ',b,shoff+i*ents) for i in range(n)];strings=b[raw[si][4]:raw[si][4]+raw[si][5]]
 sections={strings[r[0]:].split(b'\0',1)[0].decode():dict(index=i,type=r[1],flags=r[2],addr=r[3],offset=r[4],size=r[5],link=r[6],entsize=r[9],data=b[r[4]:r[4]+r[5]]) for i,r in enumerate(raw)}
 symbols=[]
 if '.symtab' in sections:
  tab=sections['.symtab'];st=raw[tab['link']];names=b[st[4]:st[4]+st[5]]
  for i in range(0,tab['size'],tab['entsize']):
   no,info,other,shndx,value,size=struct.unpack_from('<IBBHQQ',tab['data'],i);name=names[no:].split(b'\0',1)[0].decode()
   if 'r1_pool_adapter' in name and ('AUDIT_POOL_PROGRAM' in name or 'AUDIT_REGISTRY_PROGRAM' in name):
    section=next(s for s in sections.values() if s['index']==shndx);off=value-section['addr'];assert size==32 and info&15==1 and section['flags']&2 and not section['flags']&1
    symbols.append(dict(name=name,address=value,size=size,section_index=shndx,section=next(n for n,s in sections.items() if s is section),section_offset=off,bytes_hex=section['data'][off:off+32].hex()))
 return b,sections,symbols
images={k:parse(p) for k,p in paths.items()}
for k,h in expected.items():assert sha(images[k][0])==h
symbols=images['cache'][2];assert len(symbols)==2
for needle in ['AUDIT_POOL_PROGRAM','AUDIT_REGISTRY_PROGRAM']:assert sum(needle in x['name'] for x in symbols)==1
alloc=lambda ss:{n:s for n,s in ss.items() if s['flags']&2}
base=alloc(images['cache'][1]);comparisons={};slot_images={}
for kind in ['default','devnet']:
 sections=alloc(images[kind][1]);assert set(sections)==set(base)
 diffs=[]
 for name,s in sections.items():
  t=base[name];assert (s['addr'],s['size'],s['type'],s['flags'])==(t['addr'],t['size'],t['type'],t['flags'])
  for i,(a,b) in enumerate(zip(s['data'],t['data'])):
   if a!=b:diffs.append((name,i))
 allowed={(x['section'],x['section_offset']+i) for x in symbols for i in range(32)}
 assert set(diffs)<=allowed,(kind,diffs[:20])
 comparisons[kind]=dict(allocated_sections=len(sections),differing_bytes=len(diffs),differences_only_named_static_slots=True,loaded_text_sha256=sha(sections['.text']['data']))
 rows=[]
 text=sections['.text']
 for sym in symbols:
  s=sections[sym['section']];off=sym['section_offset'];content=s['data'][off:off+32];refs=[]
  for j in range(0,len(text['data'])-15,8):
   if text['data'][j]==0x18:
    value=struct.unpack_from('<I',text['data'],j+4)[0]|(struct.unpack_from('<I',text['data'],j+12)[0]<<32)
    if value in [sym['address'],sym['address']+0x100000000]:refs.append(dict(address=text['addr']+j,immediate=value,instructions_hex=text['data'][j:j+16].hex()))
  assert len(refs)==2,(kind,sym['name'],refs)
  rows.append({**sym,'bytes_hex':content.hex(),'lddw_references':refs})
 slot_images[kind]=rows
# Both deployed images execute identical instructions; differences are only named immutable slots.
assert images['default'][1]['.text']['data']==images['devnet'][1]['.text']['data']
assert any(v['differing_bytes']==0 for v in comparisons.values()),'Unstripped cache must equal at least one complete loaded image'
pins={k:dict(path=str(paths[k]),sha256=sha(v[0]),bytes=len(v[0])) for k,v in images.items()}
x=dict(status='NAMED_SYMBOL_LOADED_IMAGE_ASSOCIATION_PASS',frozen_revision='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',artifacts=pins,named_symbols=symbols,comparisons=comparisons,slots=slot_images,text_equal_default_devnet=True,no_build_performed=True,no_key_access=True,scope='Actual source-named static OBJECT symbols, immutable32-byte span, complete SHF_ALLOC image association, same text and two LDDW references per symbol. Native getter/frame/model association is a separate packet; no historical K3 pass is reused.',print_axioms='N/A: read-only ELF parser')
(B/'NHJ_RODATA.json').write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(dict(status=x['status'],artifacts=pins,comparisons=comparisons,slots={k:[dict(symbol=z['name'],address=z['address'],bytes_hex=z['bytes_hex'],references=len(z['lddw_references'])) for z in v] for k,v in slot_images.items()})))
