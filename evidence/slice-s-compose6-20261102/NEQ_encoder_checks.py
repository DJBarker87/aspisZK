"""Strict hybrid root certificate: every sequential native cut and full frames."""
import json,hashlib,re,subprocess
F='crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::encode_pool_v1_pair_forest_terminal_statement_v1'
ALTERNATIVES=['crates/aspis-core/src/field.rs::M31::to_le_bytes','crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::PoolV1PairForestTerminalPaymentV1::transition_kind','crates/aspis-statement/src/pool_v1/pair_forest_terminal.rs::transition_kind']
PAIRS=[(2,3),(4,5),(2,6),(8,9),(8,10),(11,12),(11,13),(11,14)]+[(15+2*i,16+2*i) for i in range(10)]+[(33,35),(36,37),(36,38),(36,39),(40,41),(42,43)]
THEOREMS=['NEQ_EncoderOracle.result_state_effects','NEQ_EncoderOracle.substitution','NEQ_LateBorrow.rejoin','NEQ_LateBorrow.poststate','NEQ_LateBorrow.after_preserves_child','NEQ_RootFrame.cover','NEQ_RootFrame.header_frame','NEQ_RootFrame.scalar_frame','NEQ_RootFrame.finish','NEQ_RootFrame.assembled','NEQ_RootFrame.array_ext','NEQ_EncoderDomains.reached_domains','NEQ_EncoderDomains.header_length']

def validate(c,expected,ledger,v):
 try:
  q=c['encoder_root'];assert q['function']==F
  assert q['method']=='sequential source cuts; ruling y full oracle mutation; rule B copy induction; concrete G substitution'
  assert q['domain']=='every typed terminal Statement; root physical carrier; no acceptance or inner domain premise'
  assert q['inner_hypotheses_remaining']==[] and q['trust_classification']=='P6/D188 option A reclassification'
  assert q['pairs']==[[f'NEQ_K{x:03}',f'NEQ_K{y:03}'] for x,y in PAIRS]
  assert all(v.native_pair(*pair) for pair in q['pairs'])
  from NEQ_artifacts import native_support
  attempts=sorted({a for pair in q['pairs'] for a in pair})
  assert q['native_support']==native_support(attempts)
  for r in q['native_support']:v.inherited.artifact(r)
  assert [t['name'] for t in q['theorems']]==THEOREMS and all(v.inherited.theorem(t) for t in q['theorems'])
  for r in q['manifests']:v.inherited.artifact(r)
  def patch(n):return (v.E/(f'NEQ_K{n:03}-NEQ_native_contracts.patch')).read_text()
  # Contract-fidelity shape is fixed; no arbitrary other stub_verified use admitted.
  for n in [2,3,8,9,10,11,12,13,14]:
   p=patch(n);assert 'out:&mut[u8;1520],b:bool' in p and '#[kani::modifies(out)]' in p
   assert 'impl kani::Arbitrary for PoolV1PairLatePublicStatementErrorV1' in p
   assert 'if kani::any(){Ok(())}else{Err(any_error())}' in p
  assert '#[kani::ensures(|r| !(true))]' in patch(3)
  assert '#[kani::modifies(&mut out[1])]' in patch(6)
  assert '#[kani::stub_verified(weak)]' not in patch(4) and '#[kani::stub_verified(weak)]' in patch(5)
  assert 'assert!(out[1519]==old' in patch(4) and 'assert!(out[1519]==old' in patch(5)
  assert 'let window=&mut out[144..144+1520]' in patch(8)
  assert 'let window=&mut out[145..145+1520]' in patch(9)
  assert 'assert!(output[1663]==inside' in patch(10)
  # Same actual child prestate and full arbitrary reply, not selected-byte havoc.
  p=patch(11)
  for text in ['let common=s.common();let late=&common.lane_transition','core::ptr::eq(late,&f.expected.common().lane_transition)','let window=&mut out[144..1664]','let array:&mut[u8;1520]=window.try_into().unwrap()','let reply=weak(late,array,kani::any())','f.post=out[f.j]','reply.map_err(|error|PoolV1PairForestTerminalFormatErrorV1::LaneTransition(error))?','core::ptr::eq(p,q)','pay(s,f)','let dst=&mut out[1664..]','dst[i]=src[i];i+=1','kani::assume(offset<216)','output[j]==expected_byte']:
   assert text in p,text
  assert 'let late=&f.other.common().lane_transition' in patch(12)
  assert 'pay(f.other,f)' in patch(13) and 'dst[i]=src[i]^1' in patch(14)
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+F.split('::')[0]],cwd=v.R,text=True)
  a=source.index('pub fn '+F.split('::')[1]+'(');z=source.index('\n}',a)+2;body=source[a:z]
  assert q['frozen_body']==body and q['frozen_body_sha256']==hashlib.sha256(body.encode()).hexdigest()
  assert ''.join(q['source_partition'])==body
  assert q['source_partition']==partition(body)
  for key,num in [('MASTER_OFFSET',8),('CHECKPOINT_ACCOUNT_OFFSET',40),('SELECTED_LANE_ACCOUNT_OFFSET',72),('CHECKPOINT_SEQUENCE_OFFSET',104),('HISTORICAL_ANCHOR_OFFSET',112),('LATE_STATEMENT_OFFSET',144)]:
   assert re.search(r'const '+key+r': usize = '+str(num)+r';',source)
  assert 'constPAYMENT_STATEMENT_OFFSET:usize=LATE_STATEMENT_OFFSET+POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_BYTES;' in re.sub(r'\s+','',source)
  assert 'PAYMENT_STATEMENT_OFFSET==1664&&POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES==1880' in patch(42)
  assert 'PAYMENT_STATEMENT_OFFSET==1665' in patch(43)
  starts=[0,4,5,6,7,8,40,72,104,112];widths=[4,1,1,1,1,32,32,32,8,32]
  exprs=['POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_MAGIC','POOL_V1_PAIR_FOREST_TERMINAL_VERSION','s.transition_kind() as u8','POOL_V1_DIGEST_ENCODING_VERSION','common.output_lane','common.master_account','common.checkpoint_account','common.selected_lane_account','common.checkpoint_sequence.to_le_bytes()','reply']
  for i in range(10):
   m=v.read(v.E/f'NEQ_K{15+2*i:03}-window.json');assert (m['slot'],m['mode'],m['start'],m['width'],m['expression'])==(i,'positive',starts[i],widths[i],exprs[i])
   assert m['frozen_body']==body and m['arbitrary_prestate'] and m['all_typed_inputs']
   p=patch(15+2*i)
   assert 'let old=output[j]' in p and 'let common=s.common()' in p
   if widths[i]>1:assert f'let dst=&mut output[{starts[i]}..{starts[i]+widths[i]}]' in p and 'dst[i]=src[i];i+=1' in p
   else:assert f'output[{starts[i]}]=({exprs[i]});' in p
  assert 'let d=&common.historical_global_anchor' in patch(33)
  assert 'let d=&common.lane_transition.live_snapshot.current_root' in patch(35)
  p=patch(36)
  for text in ['core::ptr::eq(s,f.expected)','child(s,f)?','let common=s.common()','core::ptr::eq(common,f.expected.common())','let output=[0u8;1880]','f.byte=output[f.j]','actual==f.reply','f.reached==actual.is_ok()','f.byte==0']:
   assert text in p,text
  assert 'fn finish(mut output:[u8;1880])->Result<[u8;1880],PoolV1PairForestTerminalFormatErrorV1>{Ok(output)}' in patch(40)
  assert 'output[0]^=1;Ok(output)' in patch(41) and 'bytes[j]==old' in patch(40)
  assert q['full_Result'] and q['ordered_effects'] and q['empty_external_modifies'] and q['same_allocation']
  assert q['loop_invariant']=='0<=i<=width; same source reply and arbitrary destination prestate; KMX loop_spec; disjoint header,late,payment intervals; arbitrary observed index; no whole-buffer protocol loop'
  rs=[r for r in ledger['rows'] if r['function']==F];obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={F}|{F+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{F+' -> '+g for r in rs for g in r['canonical_callees'] if g not in ALTERNATIVES}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False

def partition(body):
 markers=['    output[..4]','    encode_pool_v1_pair_late_public_statement_v1(','    let payment = match statement','    output[PAYMENT_STATEMENT_OFFSET..]','    Ok(output)']
 offsets=[0]+[body.index(m) for m in markers]+[len(body)]
 return [body[a:b] for a,b in zip(offsets,offsets[1:])]
