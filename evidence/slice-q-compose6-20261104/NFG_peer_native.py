"""Strict reuse of immutable NFF native windows. Never launches a prover."""
from pathlib import Path
import hashlib,json,re
from NFG_peer import load
E=Path(__file__).resolve().parent
PAIRS=[(15,16,'main_operand_reply_order'),(11,12,'main_outer_fold'),(7,8,'four_ordered_calls'),
(19,20,'sixteen_raw_products'),(21,22,'private_arbitrary_prestate_step'),(29,26,'public_full_Result_receiver'),
(31,32,'same_receiver_three_pushes'),(33,34,'actual_finish_add_return'),(45,38,'tail_argument_window'),
(41,42,'native_inner_cursor'),(43,44,'native_outer_cursor'),(46,47,'head_return_carrier'),
(48,49,'initial_arrays'),(50,51,'inner_stopped_endpoint'),(52,53,'main_decode_error'),
(54,55,'original_prefix_reference_frame'),(58,59,'same_chunk_continuation'),(60,61,'tail_decode_total'),
(62,63,'native_main_parse_window'),(64,65,'wrapper_short_prefix'),(68,69,'raw_reply_to_same_private_step'),
(70,71,'private_finish_to_public_return')]
LIMITS={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
FROZEN_LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
sha=lambda b:hashlib.sha256(b).hexdigest()
def read(d,n):return json.loads(d[n])
def name(i):return f'NFF_K{i:03}'
def target(r):c=r['native_command'];return c[c.index('--harness')+1]
def config(r):
 return {n:h for n,h in r['source_hashes'].items() if n.startswith('NFF_src/')}
def one(d,a,status):
 r=read(d,a+'/receipt.json');assert r['exit_status']==status,(a,'exit')
 assert r['limits']==LIMITS and int(r['swaps'])==0,(a,'caps/swap')
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 assert r['copy_patch_sha256']==sha((E.parent/'kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())
 assert '--locked' not in r['native_command'],'unsupported Kani flag'
 assert '--harness-timeout' in r['native_command'] and r['native_command'][r['native_command'].index('--harness-timeout')+1]=='90s'
 stdout=d[a+'/stdout.log'].decode();assert 'timed out' not in stdout.lower(),(a,'timeout')
 assert ('VERIFICATION:- SUCCESSFUL' if status==0 else 'VERIFICATION:- FAILED') in stdout,(a,'verdict')
 if status:assert 'unwinding assertion' not in stdout.lower(),(a,'unwind failure is no intended control')
 for n,h in r['source_hashes'].items():assert sha(d[a+'/sources/'+n])==h,(a,'source drift',n)
 ad=read(d,a+'-admission.json');assert ad.get('exit',ad.get('exit_status'))==0 and ad['reservation']['allowed'] is True,(a,'admission')
 graph=read(d,a+'-graph-check.json');assert graph['graph_matches_frozen'] and graph['exact_frozen_selected_graph'],(a,'graph')
 assert graph['lock_sha256']==FROZEN_LOCK
 fs=graph.get('resolved_features_all_crates',graph.get('resolved_features_all_crates',[]));assert fs,(a,'features missing')
 features={p['name']:set(p['features']) for p in fs}
 assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=features['aspis-r1-cost-probe']
 assert features['aspis-core']=={'r0'} and {'r0','pool-v1-kernel'}<=features['aspis-statement']
 assert not({'prover','cu-profiling','detail-phases'} & features['aspis-r1-cost-probe'])
 lock=read(d,a+'-lock-check.json');assert lock['unchanged'] and lock['before']==lock['after']==FROZEN_LOCK
 static=read(d,a+'-rule16-check.json');assert static['static_declarations']==[]
 return r

def check(data=None):
 d=load() if data is None else data
 assert (E/'NFG_peer_sources/NFF_RAW_SITES.json').read_bytes()==d['NFF_RAW_SITES.json'],'raw-site source drift'
 receipts=[read(d,n) for n in d if re.fullmatch(r'NFF_K\d{3}/receipt.json',n)]
 copies={}
 for r in receipts:
  h=target(r)
  if 'KMX_ptr_correct' in h or 'KMX_ptr_wrong' in h:
   copies.setdefault(json.dumps(config(r),sort_keys=True),[]).append(r)
 # Replay the committed source checker on each exact receipt payload. No live source is consulted.
 ns={'__name__':'NFG_peer_source_checker','__file__':str(E/'NFG_peer_sources/NFF_source_checks.py')}
 exec(compile(d['NFF_source_checks.py'],'NFF_source_checks.py','exec'),ns)
 out=[]
 for pos,neg,role in PAIRS:
  a,b=name(pos),name(neg);p=one(d,a,0);c=one(d,b,1)
  assert target(p)==target(c),(a,b,'renamed verdict')
  assert config(p)==config(c),(a,b,'different native payload')
  assert p['env']['RUSTFLAGS'] in c['env']['RUSTFLAGS'] and '--cfg NFF_wrong_' in c['env']['RUSTFLAGS']
  matching=copies.get(json.dumps(config(p),sort_keys=True),[])
  positive=[r for r in matching if target(r).endswith('KMX_ptr_correct') and r['exit_status']==0]
  negative=[r for r in matching if target(r).endswith('KMX_ptr_wrong') and r['exit_status']==1]
  assert positive and negative,(a,'missing exact-configuration KMX controls')
  xp,xn=positive[0],negative[0];one(d,xp['attempt'],0);one(d,xn['attempt'],1)
  assert xp['env']['RUSTFLAGS']==xn['env']['RUSTFLAGS']==p['env']['RUSTFLAGS'],(a,'KMX cfg drift')
  frozen=read(d,a+'/sources/NFF_FROZEN.json')
  payload={n[len('NFF_src/'):]:d[a+'/sources/'+n].decode() for n in p['source_hashes'] if n.startswith('NFF_src/') and n.endswith(('/NFF_dots.rs','/NFF_pairing.rs','/NFF_incoming.rs'))}
  fission=ns['check'](payload,frozen)
  out.append(dict(role=role,positive=a,negative=b,harness=target(p),kmx_positive=xp['attempt'],kmx_negative=xn['attempt'],payload_sha256=sha(json.dumps(config(p),sort_keys=True).encode()),positive_receipt_sha256=sha(d[a+'/receipt.json']),negative_receipt_sha256=sha(d[b+'/receipt.json']),source_fission=fission))
 return dict(peer_revision=json.loads((E/'NFG_PEER_IMPORT.json').read_text())['revision'],groups=out,quarantined=[],suspended=[],excluded=['NFF_K005 wrong-bound diagnostic','NFF_K025 own missing import','NFF_K030 timeout','NFF_K037 own source-pin preflight failure'])
if __name__=='__main__':
 out=check();(E/'NFG_PEER_NATIVE.json').write_text(json.dumps(out,indent=2)+'\n');print('validated',len(out['groups']),'native groups')
