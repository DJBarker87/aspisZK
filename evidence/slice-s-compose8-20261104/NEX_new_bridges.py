"""New native bridge admission followed by bottom-up composition; no open child bypass."""
from pathlib import Path
import copy,json,re,difflib
import NEX_validate as v
import NEX_raw_checks as raw
import NEX_check_box_windows as box
E=v.E
P='crates/aspis-statement/src/pool_v1/'
FUNCTIONS={**{k:val for k,val in box.FUNCTIONS.items()},'snapshotdecode':raw.F['snapshotdecode'],'late':P+'pair_tree_profile.rs::decode_pool_v1_pair_late_public_statement_boxed_v1'}
THEOREMS={
 'afterstate':['NEX_AfterstateBox.result_state_effects','NEX_AfterstateBox.child_packet','NEX_AfterstateBox.value_ext'],
 'snapshot':['NEX_SnapshotBoxOracle.result_state_effects','NEX_DecoderDomains.late_windows','NEX_BoxValueExt.snapshot'],
 'lane':['NEX_LaneOracle.result_state_effects','NEX_DecoderDomains.common_windows','NEX_BoxValueExt.late'],
 'snapshotdecode':['NEX_SnapshotParent.result_state_effects','NEX_ReadDomains.snapshot_window','NEX_ReadDomains.disjoint','NEX_DigestCallDomains.snapshot_digest','NEX_FirstError.bounded','NEX_FirstError.before','NEX_FirstError.at_error'],
 'late':['NEX_LateOracle.result_state_effects','NEX_DecoderDomains.late_windows','NEX_BoxValueExt.late'],
 'common':['NEX_CommonOracle.result_state_effects','NEX_DecoderDomains.common_windows','NEX_DecoderDomains.common_reads','NEU_DecoderProjections.common_ext']}

def cleanup(a,family,positive):
 m=v.read(E/(a+'-shape.json'));assert m['family']==family and m['mode']=='error_'+('positive' if positive else 'negative')
 snap=v.native(a,positive);source=m['source'];variant='Afterstate' if family=='afterstate' else 'Snapshot'
 assert f'(Err(PoolV1PairLatePublicStatementErrorV1::{variant}(e)),Err(expected))=>{{assert!(e==expected);assert!(f.allocated.is_null());}}' in source
 assert 'let reply=Err(' in source
 assert box.erased(m)==m['frozen_body']
 assert source in ''.join(l[1:]+'\n' for l in snap['NEX_native_contracts.patch'].splitlines() if l.startswith('+') and not l.startswith('+++'))
 return True

def late_attempt(a,mode):
 m=v.read(E/(a+'-shape.json'));assert m['mode']==mode and m['full_child_Result'] is True
 snap=v.native(a,mode=='positive');source=m['source'];path=FUNCTIONS['late'].split('::')[0];f=v.inherited.frozen_source(FUNCTIONS['late']);name=FUNCTIONS['late'].rsplit('::',1)[1];start=f.index('pub(crate) fn '+name+'(');end=f.index('\n}',start)+2;assert m['frozen_body']==f[start:end]
 if mode in ['positive','value']:
  text=m['native'].replace('fn native(','pub(crate) fn '+name+'(').replace('    bytes: &[u8],f:&mut Frame,','    bytes: &[u8],')
  text=raw.undo_call(text,'snapshot','decode_pair_live_snapshot_boxed_v1');text=raw.undo_call(text,'afterstate','decode_pair_afterstate_boxed_v1')
  text=text.replace('let out=Box::new(','Ok(Box::new(').replace('    });\n    f.allocated=&*out;\n    Ok(out)','    }))');assert text==m['frozen_body']
 assert len(m['fields'])==9 and 'slot<9' in source
 for text in ['bytes.len()==800','bytes.len()==688','f.bytes[32..].as_ptr()','f.bytes[832..].as_ptr()','f.live.map(Box::new)','f.calls==2','core::ptr::eq(&*out,f.allocated)','f.allocated.is_null()','live.next_pair_index.checked_add(1)!=Some(after.next_pair_index)']:
  assert text in source,text
 h=f+'\n#[cfg(kani)]\n#[path="NEX_late.rs"]\nmod NEX_late;\n';patch=''.join(difflib.unified_diff(f.splitlines(True),h.splitlines(True),fromfile='a/'+path,tofile='b/'+path))+'--- /dev/null\n+++ b/'+path.rsplit('/',1)[0]+'/NEX_late.rs\n@@ -0,0 +1,'+str(len(source.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in source.splitlines());assert snap['NEX_native_contracts.patch']==patch
 return True

def native_complete(kind,config):
 if kind=='snapshotdecode':return raw.complete(kind,config)
 if kind=='late':
  for mode,a in config.items():late_attempt(a,mode)
  assert set(config)=={'positive','value','allocation','argument','reply'};return True
 if kind=='common':
  assert len(config['pairs'])==15
  for slot,pair in enumerate(config['pairs']):
   for a,mode in zip(pair,['positive','value']):
    m=box.attempt(a,kind,mode);assert m['selected']==slot and m['full_child_Result'] is True
    assert 'Result<Digest,crate::AtomicStatementError>' in m['source'] and 'Result<Digest,()>' not in m['source']
  for mode in ['allocation','argument','reply']:box.attempt(config['controls'][mode],kind,mode)
  return True
 assert kind in ['afterstate','snapshot','lane']
 for mode,a in config['runs'].items():
  m=box.attempt(a,kind,mode)
  assert m['selected'] is None
  assert 'Result<Digest,()>' not in m['source']
 assert set(config['runs'])=={'positive','value','allocation','argument','reply'}
 if kind in ['afterstate','snapshot']:
  assert len(config['cleanup'])==2
  for a,positive in zip(config['cleanup'],[True,False]):cleanup(a,kind,positive)
 return True

def check(c,ledger):
 n=c['native_certificate'];kind=n['template'];f=FUNCTIONS[kind];assert n['function']==f and n['complete'] is True
 assert n['domain']=={'afterstate':'every live688-byte slice and complete typed afterstate decoder Result','snapshot':'every live800-byte slice and complete typed snapshot decoder Result','lane':'every live1520-byte slice and complete typed late decoder boxed Result','snapshotdecode':'every live800-byte slice; all bytes and every full child Result/error','late':'every live1520-byte slice; all bytes and every full child boxed Result/error','common':'every live1880-byte slice; all bytes and every full child Result/error'}[kind]
 assert n['inner_hypotheses_remaining']==[] and c['inner_hypotheses_remaining']==[]
 assert n['box_ruling_aa'] is (kind not in ['lane','snapshotdecode'])
 assert [t['name'] for t in c['domain_theorems']]==THEOREMS[kind]
 assert c['physical_theorems']==c['domain_theorems'] and c['theorems']==c['domain_theorems']
 assert c['support']==c['native_association'] and c['support']
 assert native_complete(kind,n['config'])
 import NED_validate,NEJ_validate
 assert NED_validate.certificate(c,c['subject'],ledger,{c['subject']:c['semantic_review_sha256']})
 assert NEJ_validate.call_domain(c,c['subject'],ledger)
 return True

def qualifiers(f):return ['NEX_'+f.rsplit('::',1)[1]+'.PacketDomain','NEX_'+f.rsplit('::',1)[1]+'.PhysicalInterpretation']

def compose(base,out,packet,reviewed,api):
 result=copy.deepcopy(out);by={}
 for row in result['rows']:by.setdefault(row['function'],[]).append(row)
 admitted={}
 for f,n in packet.get('NEX_new_bridges',{}).items():
  c=packet.get('members',{}).get(f)
  if f not in FUNCTIONS.values() or not api.certificate(c,f,base,reviewed):continue
  assert n==c['native_certificate']
  admitted[f]=n
  for row in by[f]:
   assert row['bridge_status']=='OPEN' and not row['named_hypotheses']
   row['bridge_status']='CLOSED-CONDITIONAL';row['selected_claims']=['NEX::'+f];row['claim_ids']=list(dict.fromkeys(row['claim_ids']+['NEX::'+f]))
   row['named_hypotheses']=[dict(name=name,statement=n['domain'] if name.endswith('.PacketDomain') else 'Root-owned valid typed immutable carrier, fresh owned Box/allocator interpretation where allocated, ABI and approved P6 transport; no inner native bridge assumed',discharged_by=None) for name in qualifiers(f)]
 # New evidence may select an actually verified new child, adding its
 # explicit domain/physical names; no old required name is removed.
 domain_view=copy.deepcopy(base)
 for row in domain_view['rows']:
  if row['function'] not in admitted:continue
  for ob in row['caller_domain_obligations']:
   g=ob.get('callee')
   if g in admitted and not ob['callee_claims']:
    ob['callee_claims']=['NEX::'+g]
    ob['callee_local_status']='CLOSED-CONDITIONAL'
    ob['required_named_hypotheses']=list(dict.fromkeys(ob['required_named_hypotheses']+qualifiers(g)))
 def accepted(c,subject,f):
  if f not in admitted:return False
  try:
   assert c['native_certificate']==admitted[f]
   return api.certificate(c,subject,domain_view,reviewed)
  except (AssertionError,KeyError,TypeError):return False
 for f in admitted:
  for row in by[f]:
   for h in row['named_hypotheses']:
    subject=f+'::'+h['name'];c=packet.get('hypotheses',{}).get(subject)
    if accepted(c,subject,f):h['discharged_by']=c['id']
   for ob in row['caller_domain_obligations']:
    subject=f+' -> '+ob['callee'] if 'callee' in ob else ob['id'];c=packet.get('edges' if 'callee' in ob else 'externals',{}).get(subject)
    if accepted(c,subject,f):ob.update(status='CLOSED',discharged_by=c['id'])
 changed=True
 while changed:
  changed=False
  for f in admitted:
   for row in by[f]:
    if row['composed_status']=='CLOSED':continue
    if any(not h['discharged_by'] for h in row['named_hypotheses']):continue
    if any(o['status']!='CLOSED' or not o['discharged_by'] for o in row['caller_domain_obligations']):continue
    if any(any(r['composed_status']!='CLOSED' for r in by[g]) for g in row['canonical_callees']):continue
    row['open_transitive_dependencies']=[g for g in row['open_transitive_dependencies'] if any(r['composed_status']!='CLOSED' for r in by[g])]
    if row['open_transitive_dependencies']:continue
    row.update(composed_status='CLOSED',composed_reason='NEX complete full-Result native bridge, every unchanged inventory edge/domain, model substitution and fresh Box/frame checks');changed=True
 allowed={'bridge_status','selected_claims','claim_ids','named_hypotheses','caller_domain_obligations','open_transitive_dependencies','composed_status','composed_reason'}
 for a,b in zip(result['rows'],out['rows']):
  if b['function'] not in admitted:assert a==b
  else:
   assert {k:w for k,w in a.items() if k not in allowed}=={k:w for k,w in b.items() if k not in allowed}
   for x,y in zip(a['caller_domain_obligations'],b['caller_domain_obligations']):assert {k:w for k,w in x.items() if k not in ['status','discharged_by']}=={k:w for k,w in y.items() if k not in ['status','discharged_by']}
 assert result['trust_rows']==base['trust_rows']
 result['NEX_new_native_admissions']=list(admitted)
 return result
