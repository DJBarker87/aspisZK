"""New native/domain admission; no promotion from a partial window collection."""
from pathlib import Path
import copy,json,hashlib,difflib
E=Path(__file__).resolve().parent;R=E.parent.parent
EXACT='crates/aspis-statement/src/pool_v1/pair_terminal.rs::exact'
sha=lambda b:hashlib.sha256(b).hexdigest()
def check(c,ledger):
 import NEX_validate as v
 n=c['native_certificate'];assert n['function']==EXACT
 assert n['domain']=='width in {8,32}; live slice length <=33; all bytes unrestricted'
 assert n['classification']=='actual frozen call, KMX, full Result, readonly state and empty runtime trace'
 assert n['inner_hypotheses_remaining']==[] and n['box_ruling_aa'] is False
 assert len(n['pairs'])==2
 assert {t['name'] for t in c['domain_theorems']+c['physical_theorems']}=={'NEX_Exact.result_state_effects'}
 assert c['domain_theorems']==c['physical_theorems']
 assert c['callee_domain_established'] is True
 assert c['required_named_hypotheses']==[]
 expected_support=set()
 for width,pair in zip([8,32],n['pairs']):
  assert len(pair)==2
  for positive,a in zip([True,False],pair):
   snapshots=v.native(a,positive);shape=v.read(E/(a+'-shape.json'))
   assert shape['width']==width and shape['mode']==('positive' if positive else 'negative')
   assert shape['domain']==n['domain']
   path=EXACT.split('::')[0];f=v.inherited.frozen_source(EXACT)
   assert shape['frozen_body']==f[f.index('fn exact<'):f.index('\n}',f.index('fn exact<'))+2]
   body=f'''use super::*;
#[kani::proof]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
#[kani::stub(<[u8]>::copy_from_slice,crate::KMX_stubs::KMX_copy_from_slice)]
fn exact_cut(){{let bytes:[u8;33]=kani::any();let len:usize=kani::any();let j:usize=kani::any();kani::assume(len<=33&&j<{width});let result=exact::<{width}>(&bytes[..len]);if len=={width}{{let out=result.unwrap();assert!(out[j]==bytes[j]{'' if positive else '^1'});}}else{{assert!(matches!(result,Err(PoolV1PairVerifierTransportErrorV1::WrongLength)));}}}}
'''
   assert shape['source']==body
   hook=f+'\n#[cfg(kani)]\n#[path="NEX_exact.rs"]\nmod NEX_exact;\n'
   patch=''.join(difflib.unified_diff(f.splitlines(True),hook.splitlines(True),fromfile='a/'+path,tofile='b/'+path))+'--- /dev/null\n+++ b/crates/aspis-statement/src/pool_v1/NEX_exact.rs\n@@ -0,0 +1,'+str(len(body.splitlines()))+' @@\n'+''.join('+'+l+'\n' for l in body.splitlines())
   assert snapshots['NEX_native_contracts.patch']==patch
   files=[a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-shape.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-source-check.json',a+'-rule16-check.json',a+'-metadata-pin.json',a+'-NEX_native_contracts.patch',a+'-NEX_oracle.patch']
   archive=a+'-inputs.json' if (E/(a+'-inputs.json.xz')).exists() else 'NEX_SOURCE_HISTORY.json'
   files.extend([archive+'.xz',archive+'.sha256'])
   expected_support.update(str((E/x).relative_to(R)) for x in files)
 assert {r['path'] for r in c['support']}==expected_support
 return True

def compose_additions(base,out,packet,reviewed,v):
 result=copy.deepcopy(out);by={}
 for row in result['rows']:by.setdefault(row['function'],[]).append(row)
 promoted=[]
 for f,cert in packet.get('NEX_native_bridge_additions',{}).items():
  # The full subject set is reconstructed from the immutable inventory.
  if f!=EXACT:continue
  try:
   rows=by[f]
   assert not any(r['canonical_callees'] for r in rows)
   subjects={f}
   for row in rows:
    subjects.update(f+'::'+h['name'] for h in row['named_hypotheses'])
    subjects.update(o['id'] for o in row['caller_domain_obligations'])
   required={f:packet.get('members',{}).get(f)}
   for row in rows:
    required.update({f+'::'+h['name']:packet.get('hypotheses',{}).get(f+'::'+h['name']) for h in row['named_hypotheses']})
    required.update({o['id']:packet.get('externals',{}).get(o['id']) for o in row['caller_domain_obligations']})
   assert set(required)==subjects
   for subject,c in required.items():
    assert v.certificate(c,subject,base,reviewed)
    assert c['native_certificate']==cert
   for row in rows:
    row['bridge_status']='CLOSED-CONDITIONAL'
    row['selected_claims']=['NEX::'+f];row['claim_ids']=list(dict.fromkeys(row['claim_ids']+['NEX::'+f]))
    for h in row['named_hypotheses']:h['discharged_by']=required[f+'::'+h['name']]['id']
    for o in row['caller_domain_obligations']:o.update(status='CLOSED',discharged_by=required[o['id']]['id'])
    assert not row['open_transitive_dependencies']
    row.update(composed_status='CLOSED',composed_reason='NEX checked reached-width exact native bridge, full Result/frame and domain certificates')
   promoted.append(f)
  except (AssertionError,KeyError,TypeError,ValueError,OSError):continue
 allowed={'bridge_status','selected_claims','claim_ids','named_hypotheses','caller_domain_obligations','composed_status','composed_reason'}
 for got,old in zip(result['rows'],out['rows']):
  if old['function'] not in promoted:assert got==old
  else:assert {k:v for k,v in got.items() if k not in allowed}=={k:v for k,v in old.items() if k not in allowed}
 assert result['trust_rows']==base['trust_rows']
 result['NEX_native_admissions']=promoted
 return result
