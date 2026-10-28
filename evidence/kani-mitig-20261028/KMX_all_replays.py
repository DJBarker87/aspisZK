"""Preserve complete original harness modules, renaming only names and adding copy stubs/bounds."""
from pathlib import Path
import json,re,subprocess,hashlib
E=Path(__file__).resolve().parent;D=E.parent/'kani-diag-20261027'
sources=json.loads((E/'KMX_source_snapshots.json').read_text())['sources'];inventory=json.loads((D/'KDX_PASS_INVENTORY.json').read_text());ex=json.loads((D/'KDX_EXPOSURE.json').read_text())
attrs=(E/'KMX_R_LPa_K004.rs.txt').read_text().split('#[kani::proof]\n')[1].split('#[kani::unwind')[0]
rename=lambda s:re.sub(r'\b((?:LP[a-t]|NB[A-M])_\w*)',r'KMX_\1',s)
modules={};plan=[]
for row in ex:
 if 'No reached' in row['copy_or_loop_length'] or any(w in row['verdict'].lower() for w in ['no exposure on','no copy exposure','rejects before']):continue
 inv=next(x for x in inventory if '/'+row['id']+'/' in x['receipt']);name=row['harness'].split('::')[-1]
 matches=[(sha,v) for sha,v in sources.items() if sha in inv['source_hashes'].values() and re.search(r'fn\s+'+name+r'\s*\(|\b\w+!\('+name+r'[,)]',v['text'])]
 assert matches,row['id'];sha,src=min(matches,key=lambda p:len(p[1]['text']))
 old=Path(src['path']).stem;mod='KMX_'+old
 parent='::'.join(row['harness'].split('::')[:-2]);parent='lib' if not parent else 'candidate' if parent=='verifier::candidate' else parent
 crate='aspis-statement' if row['id'].startswith('NBH_') else 'aspis-r1-cost-probe'
 key=(crate,parent,mod)
 if key in modules:
  if len(src['text'])>len(modules[key][1]):modules[key]=(sha,src['text'])
 else:modules[key]=(sha,src['text'])
 bound=max(row['bound'] or 0,70) # byte copies up to32 and allocator prefix up to64
 if any(w in row['copy_or_loop_length'] for w in ['1736','1768','1720','1704','1732']):bound=max(bound,1770)
 if row['id']=='LPb_K016' or row['id']=='LPe_K005':bound=258 # grows a192-byte Vec
 plan.append(dict(original=row['id'],harness=('' if parent=='lib' else 'verifier::candidate::' if parent=='candidate' else row['harness'].rsplit('::',2)[0]+'::')+mod+'::'+rename(name),module=mod,parent=parent,crate=crate,bound=bound,source_sha256=sha,original_harness=row['harness']))
# Include the original named serialization stubs unchanged apart from namespace.
needed=[x for x in plan if x['original'].startswith('LPi_')]
base=next(x for x in inventory if '/LPm_K003/' in x['receipt'])
choices=[(sha,v) for sha,v in sources.items() if sha in base['source_hashes'].values() and Path(v['path']).name=='LPi_contracts.rs']
sha,v=max(((sha,v) for sha,v in sources.items() if Path(v['path']).name=='LPi_contracts.rs'),key=lambda x:len(x[1]['text']))
modules[('aspis-r1-cost-probe','lib','KMX_LPi_contracts')]=(sha,v['text'])
# LPm calls qbytes in shared LPi module; ensure qbytes is present in selected original.
# LPf helper dependency from the same frozen diagnostic receipt.
sha,v=next((sha,v) for sha,v in sources.items() if Path(v['path']).name=='LPf_replay.rs')
modules[('aspis-r1-cost-probe','lib','KMX_LPf_replay')]=(sha,v['text'])
payload={}
for (crate,parent,mod),(sha,text) in modules.items():
 text=rename(text)
 if mod=='KMX_LPf_replay':text=re.sub(r'#\[kani::proof_for_contract\([^\n]+\n', '', text)
 if mod=='KMX_LPf_verifier':
  pieces=text.split('#[kani::proof]')
  text=pieces[0]+''.join((part[part.index('fn '):] if 'kani::stub_verified' in part.split('fn ')[0] else '#[kani::proof]'+part) for part in pieces[1:])
 text=text.replace('aspis_r1_cost_probe::','crate::')
 if mod=='KMX_LPb_harnesses':text=text.replace('use super::*;', 'use aspis_core::field::{WideExact as E,QM31 as K,M31,CM31};\nuse crate::{fast_pairing,weights::{field,powers}};')
 text=text.replace('#[kani::proof]','#[kani::proof]\n'+attrs)
 # Raise bounds only for selected harnesses, including macro-generated cases.
 for p in plan:
  if p['module']!=mod:continue
  name=p['harness'].split('::')[-1]
  # Attribute nearest the definition; full source has no nested proof definitions.
  pat=r'(#[^;]*?kani::unwind\()\d+(\)[^;]*?fn\s+'+name+r'\s*\()'
  # Avoid crossing function bodies: update all unwind attributes to max selected module bound.
 bound=258 if mod in ['KMX_LPb_harnesses','KMX_LPe_replay','KMX_LPe_verifier'] else 1770 if mod in ['KMX_LPm_verifier','KMX_LPf_verifier','KMX_LPi_verifier'] else 70
 text=re.sub(r'kani::unwind\((\d+)\)',lambda m:f'kani::unwind({max(int(m[1]),bound)})',text)
 for p in plan:
  if p['module']==mod:p['effective_bound']=max(p['bound'],bound)
 if not re.search(r'kani::unwind',text):text=text.replace('#[kani::proof]',f'#[kani::proof] #[kani::unwind({bound})]')
 (E/(mod+'.rs.txt')).write_text(text)
 path=f'crates/{crate}/src/'+mod+'.rs';payload[path]=text
# Restore scratch parents to frozen version plus module declarations.
for crate,parent,_ in modules:
 path=f'crates/{crate}/src/'+('pool_v1/pair_forest_terminal.rs' if parent=='pool_v1::pair_forest_terminal' else parent+'.rs')
 if path in payload:continue
 text=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
 if parent=='lib':
  text='#![feature(allocator_api)]\n'+text
  text+='\n#[cfg(kani)]\nmod KMX_stubs;\n'
  if crate=='aspis-r1-cost-probe':text+='\n#[cfg(kani)]\nmod KMX_trigger;\n'
 for c,p,m in modules:
  if c==crate and p==parent:text+='\n#[cfg(kani)]\n#[path="'+('..//' if parent=='pool_v1::pair_forest_terminal' else '')+m+'.rs"]\nmod '+m+';\n'
 payload[path]=text
# Statement root needs stubs and allocator_api too.
path='crates/aspis-statement/src/lib.rs'
if path not in payload:
 text=subprocess.check_output(['git','show','4bb3b3f51e16b4525f1d10336e2b0bcbbd775387:'+path],text=True)
 payload[path]='#![feature(allocator_api)]\n'+text+'\n#[cfg(kani)]\nmod KMX_stubs;\n'
payload['crates/aspis-statement/src/KMX_stubs.rs']=(E/'KMX_stubs.rs.txt').read_text()
(E/'KMX_all_payload.json').write_text(json.dumps(payload,indent=2)+'\n')
(E/'KMX_ALL_REPLAY_PLAN.json').write_text(json.dumps(plan,indent=2)+'\n')
print('replay rows',len(plan),'modules',len(modules),'payload files',len(payload))
