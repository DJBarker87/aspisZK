"""Fail-closed native capacity-family audit; partial coverage has no closure."""
from pathlib import Path
import json,hashlib,re,sys,copy
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parent.parent
sys.path.insert(0,str(E.parent/'slice-q-compose-20261029'))
import NEB_validate as neb
obj=lambda p:json.loads(Path(p).read_text())
sha=lambda p:hashlib.sha256(Path(p).read_bytes()).hexdigest()
require=neb.require
TARGET='verifier::NEV_prefix_step::prefix_push_fixed_offsets'
F='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
def pair(a,b):
 p=obj(E/a/'receipt.json');n=obj(E/b/'receipt.json')
 require(p['exit_status']==0 and n['exit_status']==1,'native/control verdict')
 require(p['kind']==n['kind']=='kani' and p['module']==n['module']==TARGET,'wrong native target')
 require(p['source_hashes']==n['source_hashes'],'changed control source')
 require(p['native_command']==n['native_command'],'changed control command')
 pe=copy.deepcopy(p['env']);ne=copy.deepcopy(n['env'])
 require(ne.pop('RUSTFLAGS')==pe.pop('RUSTFLAGS')+' --cfg NEV_wrong_fixed_offsets' and pe==ne,'control configuration drift')
 require(p['copy_patch_sha256']==n['copy_patch_sha256']==KMX,'wrong KMX patch pin')
 require(sha(R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch')==KMX,'KMX patch changed')
 for a,d in [(a,p),(b,n)]:
  require(d['swaps']=='0' and d['limits']==dict(zip(['memory.high','memory.max','memory.swap.max','pids.max'],['6442450944','8589934592','0','64'])),'scope limits')
  require(d['source_revision'] and d['peak_rss_kib'] and d['wall_seconds']>=0,'missing section6 metrics')
  require(d['print_axioms']=='N/A: kani','wrong audit kind')
  for name,h in d['source_hashes'].items():require(sha(E/a/'sources'/name)==h,'archived input differs')
  for suffix in ['-graph-check.json','-frozen-source-check.json','-lock-check.json','-rule16-check.json','-tool-check.json']:
   require((E/(a+suffix)).is_file(),'missing gate '+suffix)
  g=obj(E/(a+'-graph-check.json'));require(g['graph_matches_frozen'] and g['resolved_features_all_crates'],'frozen graph/features not validated')
  l=obj(E/(a+'-lock-check.json'));require(l['unchanged'] and l['before']==l['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef','lock drift')
  require(obj(E/(a+'-frozen-source-check.json'))['passed'],'frozen source erasure failed')
  require(obj(E/(a+'-rule16-check.json'))['static_declarations']==[],'writable static')
  for name in ['NEV_prefix_step.rs','NEV_dot_ctor.rs','NEV_row_step.rs']:
   src=E/a/'sources/NEV_src/crates/aspis-r1-cost-probe/src'/name
   require(not re.search(r'\bstatic\s+(?:mut\s+)?[A-Za-z_]',src.read_text()),'static in harness')
  ad=obj(E/(a+'-admission.json'));require(ad['exit']==0 and ad['reservation']['allowed'] is True,'launch not admitted')
 for suffix in ['-graph-check.json','-tool-check.json']:
  require(obj(E/(p['attempt']+suffix))==obj(E/(n['attempt']+suffix)),'pair gate drift '+suffix)
 positive=(E/p['attempt']/'stdout.log').read_text();negative=(E/n['attempt']/'stdout.log').read_text()
 require('VERIFICATION:- SUCCESSFUL' in positive and re.search(r'\*\* 0 of \d+ failed',positive),'positive did not prove property')
 require('VERIFICATION:- FAILED' in negative and re.search(r'\*\* 1 of \d+ failed',negative),'negative did not fail intended assertion')
 require('core::panicking::assert_failed_inner' in negative,'negative assertion not reached')
 require('timed out' not in negative and 'CBMC failed' not in negative,'negative timeout/no verdict')
 source=(E/p['attempt']/'sources/NEV_src/crates/aspis-r1-cost-probe/src/NEV_prefix_step.rs').read_text()
 # Only the final, actually reached same-name harness is considered.
 require(source.count('fn prefix_push_fixed_offsets()')==1,'renamed/duplicate target')
 require(source.count('fn NEV_append_fixed_capacity<const CAP:usize>()')==1,'wrong prestate setup')
 body=source[source.index('// Exact Kani arbitrary initialized allocation.'):]
 require('exact_vec::<M31,CAP>()' in body and 'before.truncate(index)' in body,'restricted/invalid prestate')
 require('before.push(product)' in body and 'observed<=index' in body and 'index<CAP' in body,'actual push/window missing')
 require('before.len()==index+1 && before.capacity()==CAP && before.as_ptr()==pointer' in body,'incomplete metadata projection')
 require('if observed<index{before[observed].0}else{product.0}' in body and 'let after=before[observed].0' in body,'append/frame observation missing')
 require('if cfg!(NEV_wrong_fixed_offsets){old^1}else{old}' in body,'wrong matched control')
 require(not re.search(r'Option\s*<\s*fn|\bfn\s*\([^)]*\)\s*->|stub_verified|proof_for_contract|product_reply|\.mul\(',body),'unapproved arithmetic/function-pointer/contract dependency')
 caps=sorted(map(int,re.findall(r'^ (\d+)=>NEV_append_fixed_capacity::<\d+>\(\),$',body,re.M)))
 require(caps and len(caps)==len(set(caps)),'missing/duplicate capacities')
 require(all(f'{c}=>NEV_append_fixed_capacity::<{c}>(),' in body for c in caps),'capacity argument mismatch')
 return caps

def audit(campaign=None):
 campaign=obj(E/'NEV_PREFIX_CAMPAIGN.json') if campaign is None else campaign
 require(campaign['pending']==[],'native capacity campaign incomplete')
 seen=set();pairs=[]
 for item in campaign['accepted']:
  caps=pair(item['positive'],item['negative'])
  require(caps==list(range(item['lo'],item['hi']+1,item['stride'])),'partition record differs from proof source')
  require(not seen.intersection(caps),'overlapping native partition')
  seen.update(caps);pairs.append(dict(**item,proved_capacities=caps))
 expected=set(range(5,111,5));require(expected<=seen,'missing reachable caller capacity')
 require(all(1<=c<=110 for c in seen),'invented capacity domain')
 proofs=[dict(receipt=str((E/'NEV_L008/receipt.json').relative_to(R)),receipt_sha256=sha(E/'NEV_L008/receipt.json'),theorems=['NEV_PrefixAssembly.windows','NEV_PrefixAssembly.active','NEV_PrefixCapacity.representative','NEV_PrefixCallerDomain.gathered','NEV_PrefixCallerDomain.capacities','NEV_PrefixCalls.m31_site','NEV_PrefixCalls.member','NEV_PrefixCalls.cases','NEG_PrefixAssociation.step','NEG_PrefixAssociation.source','NEI_PrefixProduct.actual','NEI_PrefixStep.total'])]
 for proof in proofs:
  for theorem in proof['theorems']:neb.check_receipt(proof,theorem)
 return dict(status='NATIVE_PREFIX_CAPACITY_FAMILY_CHECKED',frozen_revision=F,domain='flat length=5*k,0<k<=22; every raw U32 input; arbitrary valid live prefix index<capacity and observation<=index',pairs=pairs,reachable_capacities=sorted(expected),extra_capacities=sorted(seen-expected),lean_evidence=proofs,trust='P6/D188 option A semantic transport retained; reclassification, never removal',composed_rows_closed=[],remaining=['native/library no-growth footprint review','full root packet and callee certificates','incoming gather native same-call association'])
if __name__=='__main__':
 result=audit();(E/'NEV_PREFIX_NATIVE_REVIEW.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(dict(status=result['status'],capacities=len(result['reachable_capacities']))))
