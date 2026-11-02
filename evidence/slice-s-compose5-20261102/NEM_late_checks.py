"""Late caller: full mutation, exact child Results/order and framed suffix."""
import json,hashlib,subprocess
import NEM_contract_checks as contracts
F='crates/aspis-statement/src/pool_v1/pair_tree_profile.rs::encode_pool_v1_pair_late_public_statement_v1'
FIDELITY={'contract':'NEM_K089','real':'NEM_K090','unimplied':'NEM_K091','inverted':'NEM_K092','frame':'NEM_K093','oracle_contract':'NEM_K094','oracle_inverted':'NEM_K095','caller':'NEM_K096','wrong_window':'NEM_K097','inside_unimplied':'NEM_K098'}
HEADERS=[['NEJ_K040','NEJ_K041'],['NEJ_K042','NEJ_K043'],['NEJ_K044','NEJ_K045'],['NEJ_K046','NEJ_K047'],['NEJ_K048','NEJ_K049']]
NEL_PAIRS=[['NEL_K008','NEL_K009'],['NEL_K010','NEL_K011'],['NEL_K016','NEL_K017'],['NEL_K050','NEL_K051'],['NEL_K052','NEL_K053']]

def support(v):
 from NEM_artifacts import ref,native_support
 out=native_support(['NEM_K037','NEM_K038','NEM_K084','NEM_K085',*FIDELITY.values(),'NEM_K099','NEM_K100','NEM_K101'])
 for folder,prefix,pairs in [('slice-s-compose3-20261101','NEJ_',HEADERS),('slice-s-compose4-20261101','NEL_',NEL_PAIRS)]:
  P=v.R/'evidence'/folder
  out += [ref(P/n) for pair in pairs for a in pair for n in [a+'/receipt.json',a+'/stdout.log',a+'.json',a+'-admission.json',a+'-graph-check.json',a+'-lock-check.json',a+'-metadata-pin.json',a+'-source-check.json',a+'-rule16-check.json',a+'-'+prefix+'native_contracts.patch',a+'-'+prefix+'oracle.patch']]
 return out

def validate(c,expected,ledger,v):
 try:
  q=c['late_composition'];assert q['function']==F
  assert q['method']=='ruling y: full fixed800-view mutation oracle, native tail, KMX suffix induction and concrete child substitution'
  assert q['all_typed_inputs'] and q['all_slice_lengths'] and q['full_Result_state_order']
  assert q['trust_classification']=='P6/D188 option A reclassification'
  assert q['fidelity']==FIDELITY and contracts.fidelity(q['fidelity'],v)
  assert q['tail']==['NEM_K099','NEM_K100','NEM_K101']
  assert all(contracts.run(a,a=='NEM_K099',v) for a in q['tail'])
  assert v.native_pair('NEM_K037','NEM_K038') and v.native_pair('NEM_K084','NEM_K085')
  for folder,prefix,pairs in [('slice-s-compose3-20261101','NEJ_',HEADERS),('slice-s-compose4-20261101','NEL_',NEL_PAIRS)]:
   assert all(v.native_pair(*p,folder=v.R/'evidence'/folder,prefix=prefix) for p in pairs)
  assert q['native_support']==support(v)
  for r in q['native_support']:v.inherited.artifact(r)
  assert q['mutation']=='every byte of actual [32,832) may change, including on child Err; all outside bytes framed'
  assert q['array_view']=='NEM_ArraySnapshotView.cover: every length800 Slice poststate is the SAME fixed-array view value; native pointer equality checked'
  assert q['legacy_decode_qualification']=='direct encoder source proof has no decode premise and reaches no decoder; decoder row stays unchanged'
  source=subprocess.check_output(['git','show',ledger['frozen_revision']+':'+F.split('::')[0]],cwd=v.R,text=True)
  a=source.index('pub fn encode_pool_v1_pair_late_public_statement_v1(');z=source.index('\n}',a)+2;body=source[a:z]
  assert q['frozen_body']==body and q['frozen_body_sha256']==hashlib.sha256(body.encode()).hexdigest()
  assert 'statement.live_snapshot.next_pair_index.checked_add(1)' in body and 'output.fill(0);' in body
  assert '&mut output[32..32 + POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES]' in body
  assert body.index('encode_pool_v1_pair_live_snapshot_v1(')<body.index('encode_pool_v1_pair_verified_afterstate_v1(')<body.index('copy_from_slice(&encoded_afterstate)')
  assert body.count('.to_le_bytes()')==4 and 'encode_digest_canonical(' not in body and 'decode_' not in body
  assert q['theorem_names']==['NEM_SnapshotBorrow.rejoin','NEM_SnapshotBorrow.poststate','NEM_SnapshotBorrow.after_preserves_child','NEM_ArraySnapshotView.cover','NEM_ArraySnapshotView.poststate','NEM_LateOracle.tail_substitution','NEM_LateOracle.run_substitution','NEM_LateOracle.value_and_frame','NEM_LateOracle.late_reached']
  assert [t['name'] for t in q['theorems']]==q['theorem_names'] and all(v.inherited.theorem(t) for t in q['theorems'])
  def code(a):return (v.E/(a+'-NEM_native_contracts.patch')).read_text()
  assert 'let reply=weak(&s.live_snapshot,array,kani::any());f.live=reply;f.calls=1;f.post=out[f.j];' in code('NEM_K099')
  assert 'child_after(&s.candidate_afterstate,f)' in code('NEM_K099') and 'child_after(f.other,f)' in code('NEM_K100')
  assert 'dst[i]=src[i]^1' in code('NEM_K101') and 'dst[i]=src[i];' in code('NEM_K099')
  assert 'f.calls==if f.live.is_err(){1}else{2}' in code('NEM_K099') and 'else{f.post}' in code('NEM_K099')
  assert '#[kani::ensures(|r| true)]' in code('NEM_K099')
  rs=[r for r in ledger['rows'] if r['function']==F];obs=[o for r in rs for o in r['caller_domain_obligations']]
  allowed={F}|{F+'::'+h['name'] for r in rs for h in r['named_hypotheses']}|{F+' -> '+g for r in rs for g in r['canonical_callees']}|{o['id'] for o in obs if 'callee' not in o}
  assert expected in allowed
  if c['kind']=='alternative-resolution':
   assert expected in {F+' -> crates/aspis-core/src/field.rs::M31::to_le_bytes',F+' -> crates/aspis-core/src/field/wide_exact.rs::WideExact::to_le_bytes'}
   assert '(POOL_V1_PAIR_LATE_PUBLIC_STATEMENT_HEADER_BYTES as u16).to_le_bytes()' in body
   assert '(POOL_V1_PAIR_LIVE_SNAPSHOT_BYTES as u32).to_le_bytes()' in body
  return True
 except (AssertionError,KeyError,ValueError,TypeError,OSError):return False
