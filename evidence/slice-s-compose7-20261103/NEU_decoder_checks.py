"""Strict additional admission for the two216-byte boxed decoder helpers."""
import json,re,hashlib,difflib
from pathlib import Path
D='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::'
FUNCTIONS=[D+'decode_'+n+'_statement_boxed_v1' for n in ['transfer','withdrawal']]
DOMAIN='every typed common and live216-byte payment slice; every child Result and payment error'
THEOREMS={}
for n in ['transfer','withdrawal']:
 THEOREMS['decode_'+n+'_statement_boxed_v1']=['NEU_BoxDecodeModel.'+n+'_result_state_effects','NEU_DecoderProjections.common_ext','NEU_DecoderProjections.'+n+'_ext','NEU_DecoderProjections.payment_packet']
sha=lambda b:hashlib.sha256(b).hexdigest()
def pair(v,attempts):
 import NEQ_validate,NEU_bridge_checks as b
 assert len(attempts)==2 and NEQ_validate.native_pair(*attempts,folder=v.E,prefix='NEU_')
 for a in attempts:
  r=v.read(v.E/a/'receipt.json');cfg=v.read(v.E/(a+'.json'));snapshots=b.inputs(v.E,a)
  assert all(r[k]==w for k,w in cfg.items())
  assert set(snapshots)==set(r['source_hashes']) and all(sha(s.encode())==r['source_hashes'][n] for n,s in snapshots.items())
  for n in ['NEU_native_contracts.patch','NEU_oracle.patch']:assert snapshots[n]==(v.E/(a+'-'+n)).read_text()
  assert cfg['native_command'][cfg['native_command'].index('--manifest-path')+1].endswith('/crates/aspis-statement/Cargo.toml')
  features={p['name']:set(p['features']) for p in v.read(v.E/(a+'-metadata-pin.json'))['features_all_crates']}
  assert set(cfg['required_statement_features'])<=features['aspis-statement']
  source=snapshots['NEU_native_contracts.patch'];path=D.split('::')[0];frozen=v.frozen_source(D+'hook');changed=frozen+'\n#[cfg(kani)]\n#[path="NEU_box_decode.rs"]\nmod NEU_box_decode;\n'
  hook=''.join(difflib.unified_diff(frozen.splitlines(True),changed.splitlines(True),fromfile='a/'+path,tofile='b/'+path))
  assert source.startswith(hook)
  assert all(x in ['core::ptr::copy_nonoverlapping','<[u8]>::copy_from_slice'] for x in re.findall(r'kani::stub\(([^,]+),',source))
  assert not any(x in source for x in ['stub_verified','proof_for_contract','kani::requires','static mut','UnsafeCell','Cell<','Atomic','transmute','unsafe{'])
 return True

def addition(b,f,ledger,v,reviewed):
 try:
  import NEU_bridge_checks as checks
  assert f in FUNCTIONS and b['function']==f
  assert b['semantic_review_sha256']==reviewed['native-bridge::'+f]==sha(json.dumps({k:w for k,w in b.items() if k!='semantic_review_sha256'},sort_keys=True).encode())
  assert b['frozen_revision']==ledger['frozen_revision'] and b['domain']==DOMAIN
  assert b['trust_classification']=='P6/D188 option A reclassification' and b['new_trust_rows']==[] and b['inner_hypotheses_remaining']==[]
  assert all(b[k] is True for k in ['full_Result','same_inputs','same_state','same_ordered_effects','native_frame_complete'])
  assert b['physical_qualification']=='root-owned valid typed carriers, fresh Box allocation/cleanup interpretation and ABI; no inner native bridge assumed'
  name=f.rsplit('::',1)[1];branch='transfer' if name=='decode_transfer_statement_boxed_v1' else 'withdrawal'
  assert [t['name'] for t in b['theorems']]==THEOREMS[name] and all(v.inherited.theorem(t) for t in b['theorems'])
  pairs=b['native_pairs'];assert len(pairs)==1 and pair(v,pairs[0])
  required=set()
  for a in pairs[0]:
   required.update(str((v.E/n).relative_to(v.R)) for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-NEU_native_contracts.patch',a+'-NEU_oracle.patch',a+'-shape.json',a+'-inputs.json.xz',a+'-inputs.json.sha256'])
  assert {r['path'] for r in b['support']}==required
  for r in b['support']:v.inherited.artifact(r)
  frozen=v.frozen_source(f);start=frozen.index('fn '+name+'(');end=frozen.index('\n}',start)+2;body=frozen[start:end]
  assert b['frozen_body']==body and b['frozen_body_sha256']==sha(body.encode())
  fields=['common.'+x for x in checks.COMMON]+['public.'+x for x in checks.PUBLIC+(['recipient_commitment[i].0'] if branch=='transfer' else ['amount','destination_token_account[j]'])]
  for a,mode in zip(pairs[0],['positive','negative']):
   m=v.read(v.E/(a+'-shape.json'));assert m['branch']==branch and m['mode']==mode and m['fields']==fields and m['frozen_body']==body
   assert m['domain']=='every typed common, arbitrary live216 bytes and complete arbitrary typed public/error reply; arbitrary field/byte/word/frontier index'
   erased=m['native'].replace('fn native(','fn '+name+'(').replace('\nf:&mut Frame)','\n)').replace('decode(payment,f)','decode_pool_v1_'+('private_transfer' if branch=='transfer' else 'withdrawal')+'_public_v1(payment)')
   assert erased==body
   source=(v.E/(a+'-NEU_native_contracts.patch')).read_text();fragment=source.split('+++ b/crates/aspis-statement/src/pool_v1/NEU_box_decode.rs\n',1)[1]
   added='\n'.join(l[1:] for l in fragment.splitlines() if l.startswith('+'))+'\n'
   assert sha(added.split('\nstruct Frame',1)[0].replace('crate::','aspis_statement::').encode())==checks.HELPERS_SHA256
   start=added.index('fn native(');end=added.index('\n}',start)+2;assert added[start:end]==m['native']
   assert re.findall(r'kani::assume\((.*?)\)',source)==['false','i<8&&j<32&&k<20&&slot<'+str(len(fields))]
   left='match slot{'+','.join(str(i)+'=>'+x+' as u64' for i,x in enumerate(fields))+',_=>0}'
   right=left.replace('common.','expected_common.').replace('public.','expected_public.')
   if mode=='negative':right=right.replace('expected_common.master_account[j] as u64','expected_common.master_account[j] as u64^1')
   assert 'assert!(('+left+')==('+right+'));' in source
   for text in ['bytes.len()==216','core::ptr::eq(bytes.as_ptr(),f.bytes.as_ptr())','f.calls=1;f.reply','assert!(f.calls==1)','(Err(PoolV1PairForestTerminalFormatErrorV1::Payment(e)),Err(expected))=>assert!(e==expected)']:
    assert text in source,text
  return True
 except (AssertionError,KeyError,TypeError,ValueError,OSError):return False
