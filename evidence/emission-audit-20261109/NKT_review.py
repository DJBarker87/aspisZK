#!/usr/bin/env python3
"""Join the mechanical inventory to explicit, reviewable manual classifications."""
import collections,hashlib,json,lzma,pathlib,re,subprocess,time
from NKT_checker import Git,sha,sites,FROZEN
from NKT_source_scan import mask,scan,function_span
P=pathlib.Path(__file__).parent

def family(name):
 if 'batch_tree' in name:return ('CONFIRMED_LOST_RESULT','Post-loop node_count ? / Parse guard / verify_in_place rejection lose Err into none; outer caller fails panic. Frozen candidate.rs:196/200/203; NJS raw:966/980/992/997 ->1046. Ruling bc(1).')
 if 'canonical_scan' in name:return ('FALSE_POSITIVE_PROPAGATION','Inner normal completion has control tag 1; tags 0 propagate some Err. The outer exhaustion tail explicitly produces some (Ok ()). Frozen candidate.rs:54-73; NKL_ScanModel.source and NKL_CanonicalInstallation.source prove full Result on width57607.')
 if 'verify_in_place' in name:return ('FALSE_POSITIVE_PROPAGATION','Exhaustion tail constructs some Bool on each arm; none is a nested pending-return propagation arm, not a discarded tail. Frozen multiproof.rs:138-198; NJA raw verify_in_place_loop0.body. NJV_TX1.TX1_127/NJV_TX2.TX2_093 roots concern its Bool/Scratch, not batch_tree.')
 if 'validate_checkpoint_queries' in name or name=='validate_loop.body':return ('FALSE_POSITIVE_VALUE_ENCODED_BY_NONE','The two in-loop guards use none as Err(Checkpoint); caller maps none to precisely that error. Frozen verifier.rs:352-360; NJC_ValidateEmission.verifier.validate_checkpoint_queries:51-60; Port5Q2_ReaderValidate.reference.')
 if name.startswith('validate_ref_'):return ('FALSE_POSITIVE_VALUE_ENCODED_BY_NONE','Inner rejection returns tag 0 and outer done(i,none); caller constructs NonCanonical(row,i). Tail exhaustion is some (Ok ()). NCO reference NCO_K016/sources/NCO_src/crates/aspis-r1-cost-probe/src/NCO_reference.rs:18-29 and NCO_EXTRACT pins.')
 if name=='weights_loop.body':return ('FALSE_POSITIVE_NORMAL_COMPLETION','IterMut exhaustion returns (at,none,back im); caller constructs Ok(weights,at), while Reader.k errors are some residual. Frozen verifier.rs:363-371; Port5Q2_ReaderWeights.weights and weights_loop.body.')
 if 'Transcript.challenge_qm31' in name:return ('FALSE_POSITIVE_NORMAL_COMPLETION','None is normal outer IterMut exhaustion, followed by reconstruction of QM31 from the returned limbs. Error residuals are preserved as some r; frozen transcript.rs:409-447, emitted caller challenge_qm31. Historical sampler source/version pin remains separate.')
 if 'QueryScan.scan' in name:return ('FALSE_POSITIVE_VALUE_ENCODED_BY_NONE','In-loop stop guards use none; caller returns true. Exhaustion explicitly returns some false. Frozen r0_transcript.rs:202-214.')
 if name in ['digest_loop.body','eq_digest_loop.body','equal_loop.body','zero_loop.body','valid_sequences_loop.body','zero_sequences_loop.body']:
  return ('FALSE_POSITIVE_NORMAL_COMPLETION','none is normal loop exhaustion; caller returns Ok(out) for digest or true for predicates. In-loop failure is some Err/false. NCV_reference.rs:15-21,77-78; decoder native correspondence remains inherited, not re-proved.')
 if name=='control_ref_loop.body':return ('FALSE_POSITIVE_NORMAL_COMPLETION','Iterator exhaustion returns none; caller explicitly returns (Ok(()),calls). Early error carries some(Err(Parse),calls). NHM_control_reference.rs.patch:2-5.')
 if name in ['anyBody','owned_checkpoint_nonzero_loop.body','prefix_different_loop.body']:
  return ('FALSE_POSITIVE_NORMAL_COMPLETION','Iterator/scan exhaustion is false; early matching element is some true. Caller supplies false for none. This is an any/nonzero predicate, not discarded Result. S2StdAnySourceV1.any; S2OwnedStage1ModelV1.owned_checkpoint_nonzero; S2SdkProofGateModelV1.prefix_different.')
 if 'require_distinct_accounts' in name or 'require_zero' in name:return ('FALSE_POSITIVE_NORMAL_COMPLETION','none is normal exhaustion; caller constructs Ok(()). In-loop account/zero rejection carries some Err. Frozen r1_pool_adapter_owned.rs:59-82; AdapterRwModel matching caller.')
 if 'check_values_owned' in name:return ('FALSE_POSITIVE_NORMAL_COMPLETION','Canonicality errors preserve some residual; normal exhaustion none is mapped to Ok(()). Frozen compact.rs:139-144; S8OwnedP6.check_values_owned caller.')
 if 'decode_k_loop' in name:return ('FALSE_POSITIVE_NORMAL_COMPLETION','Iterator exhaustion carries output array plus none; caller constructs Ok(output). In-loop ? residual carries some r. Frozen r1_wire.rs::ValidatedRecord::decode_k; AspisR1DecodeKFullV10.Funs matching caller.')
 if 'finish_query_dot' in name or 'owned_claim_loops' in name:return ('FALSE_POSITIVE_NORMAL_COMPLETION','none signals loop exhaustion and the caller executes the normal finishing/sum continuation; every in-loop ? returns some residual. Frozen verifier.rs:301-306 for finish_query_dot; S1ClaimOwnedNestedModelV1 and S1ClaimBorrowedAbiNativeV1 loop/caller definitions for outlined claims reference.')
 if any(n in name for n in ['BatchedWeights.finish','update_residue_row','WideExact.to_le_bytes']):return ('FALSE_POSITIVE_WRITEBACK_OPTION','none is passed to iterator next_back during normal borrow writeback, inside a returned function; it is not a pending Result value. Frozen verifier.rs:226/235-245 and field/wide_exact.rs::to_le_bytes; corresponding emitted definitions.')
 return ('UNREVIEWED_CANDIDATE','No manual family classification; do not infer fidelity or row status.')

def main():
 start=time.monotonic();a=json.load(open(P/'NKT_AUDIT.json'));g=Git(a['audit_revision']);imp=json.loads(lzma.open(P/'NKT_IMPORTS.json.xz').read())['modules']
 ledger=json.loads(lzma.decompress(g.read('evidence/ledger19-20261108/NKN_LEDGER.json.xz')));rows=ledger['rows']
 source_cache={};masked={};span_cache={};scan_cache={};post={};reviews=[]
 # Recovery source hashes supplement, but never replace, the recorded object pins.
 host=json.loads(lzma.open(P/'NKT_HOST_SOURCES.json.xz').read())
 a['host_recovered_sources']=[{k:v for k,v in r.items() if k!='source'} for r in host['files']]
 for x in a['functions']:
  old=x.get('emitter_span_sha256',x['frozen_body_sha256']);x['emitter_span_sha256']=old;x['frozen_body_sha256']=None
  p=x['source_path'];symbol=x['rust_symbol'];span=None
  original=p
  if p and symbol:
   if p.startswith('src/statement/'):
    p='crates/aspis-statement/src/'+p[len('src/statement/'):]
   elif not p.startswith(('crates/','programs/','/')):
    if symbol.startswith('aspis_core::') and p.startswith(('src/','field')):
     p='crates/aspis-core/'+(p if p.startswith('src/') else 'src/'+p)
    elif symbol.startswith('aspis_statement::') and p.startswith('src/'):
     p='crates/aspis-statement/'+p
    elif symbol.startswith('aspis_r1_cost_probe::') and p.startswith('src/'):
     p='crates/aspis-r1-cost-probe/'+p
  x['source_path']=p
  if original!=p:x['emitter_source_path']=original;x['source_resolution']='crate-qualified path alias; source revision still must be checked'

  if p and symbol:
   if p not in source_cache:
    z=subprocess.run(['git','show',FROZEN+':'+p],capture_output=True);source_cache[p]=z.stdout.decode() if z.returncode==0 else None
   src=source_cache[p];name=symbol.split('::')[-1]
   if src and re.fullmatch(r'[A-Za-z_]\w*',name):
    key=(p,name,x['source_lines'][0]);
    if key not in span_cache:
     # function_span's whole-file mask is cached independently of function name.
     if p not in masked:masked[p]=mask(src)
     text=masked[p];ms=list(re.finditer(r'\bfn\s+'+re.escape(name)+r'\b',text))
     result=None
     if ms:
      m=min(ms,key=lambda z:abs(text.count('\n',0,z.start())+1-key[2]));br=text.find('{',m.end());depth=0
      for en in range(br,len(text)):
       if text[en]=='{':depth+=1
       elif text[en]=='}':
        depth-=1
        if depth==0:
         result={'start_line':text.count('\n',0,m.start())+1,'end_line':text.count('\n',0,en)+1,'text':src[m.start():en+1]};break
     span_cache[key]=result
    span=span_cache[key]
  if span:
   x['frozen_body_sha256']=sha(span['text'].encode());x['frozen_hash_scope']='fn keyword through matching closing brace, exact frozen bytes'
   x['frozen_source_lines']=[span['start_line'],span['end_line']]
   key=(p,span['start_line'],span['end_line'])
   if key not in scan_cache:scan_cache[key]=scan(span['text'],span['start_line'])
   x['source_scan']=scan_cache[key]
   if x['source_scan']['post_loop_exit_candidates']:post.setdefault(key,{'path':p,'lines':x['frozen_source_lines'],'definitions':set(),'scan':x['source_scan']})['definitions'].add(x['definition'])
  else:
   x['frozen_hash_scope']='not mapped: reference/library/helper or missing source annotation; no native-fidelity certification'
   x['source_scan']=None
  flags=[d for d in x['sites'] if d['done_none']]
  if flags:
   verdict,reason=family(x['definition']);x['verdict']=verdict;x['review_reason']=reason
   for d in flags:reviews.append({'emission_path':x['emission_path'],'definition':x['definition'],'line':d['line'],'sites':d['done_none'],'verdict':verdict,'reason':reason,'source_path':p,'frozen_source_lines':x.get('frozen_source_lines')})
  else:x['verdict']='NO_PENDING_RETURN_LOSS_PATTERN'
  # Do not promote a no-hit to a semantic-equivalence certificate.
  x['general_fidelity_proved']=False
 # Exact known post-loop cases in release-related sources. Direct Result transport is retained.
 post_reviews=[]
 for (p,lo,hi),v in post.items():
  v['definitions']=sorted(v['definitions']);txt=source_cache[p].splitlines();excerpt='\n'.join(txt[lo-1:hi])
  n=' '.join(v['definitions'])
  if 'batch_tree' in n:verdict='CONFIRMED_LOST_RESULT';why='Frozen errors196/200/203 vs NJS966/980/992/997 and1046.'
  elif 'Transcript.challenge_qm31' in n:verdict='PRESERVED_NESTED_POST_LOOP_RESULT';why='Failure after the inner retry loop is some(Result.Err()), outer exhaustion none executes normal QM31 reconstruction. AspisR72Sampler.Funs challenge_qm31_loop0.body explicitly retains Err; frozen transcript.rs:434.'
  elif 'canonical_scan' in n:verdict='FALSE_POSITIVE_NESTED_LOOP';why='All candidates are still inside an enclosing loop; no explicit outer post-loop exit. Tail Ok is preserved. NKL_ScanModel.source.'
  elif 'QueryGeometry.for_range' in n:verdict='PRESERVED_DIRECT_RESULT';why='Empty-flat post-loop return is direct done(Result.Ok record), not Option none; Port3_NativeGeometryBody:296-300; later inversion loop also returns full record.'
  elif 'expand_semantic' in n:verdict='PRESERVED_DIRECT_RESULT';why='Post-loop source/destination checks emit direct done(Err Length,out), and success done(Ok(),out); S1NativeCompactModelV1:142-151.'
  elif 'verify_finish' in n:verdict='DEPLOYED_FEATURE_FALSE_POSITIVE';why='The loops are all cfg(feature=prover); deployed verifier excludes that block. NJG raw has no rust_loop; EqualCirclePoints Err and payload ? retain ordinary returned Results.'
  elif 'process_r1_cost_probe_instruction' in n:verdict='DEPLOYED_FEATURE_FALSE_POSITIVE';why='Every loop in the instruction entry lies inside cfg(not(feature=pool-adapter)); deployed program enables pool-adapter and returns r1_pool_adapter::process before that block. Frozen lib.rs:57-68. Entry rows remain OPEN independently.'
  elif 'Weights.pair' in n:verdict='PRESERVED_DIRECT_RESULT';why='The expected_n loop returns Usize directly; its caller performs the length guard and allocations with explicit Result. Later errors likewise use direct Result, not pending none. FIo_Native.weights.Weights.pair_loop0.body and matching pair definition in RPz7_FIo_NativeFuns; TX2:129 root is AspisR1.NJF_PairInstantiation.source. Historical source/version identity is a separate pin check.'
  else:verdict='SOURCE_REVIEW_REQUIRED';why='Imported historical native body or unmatched active extraction; retained as audit gap, not declared faithful.'
  v.update(verdict=verdict,reason=why);post_reviews.append(v)
 # Verify the negative tail controls mechanically, retaining raw internal warnings.
 checks={}
 controls=[('canonical_scan','evidence/batch-merkle-20261108/NJS_emitted/raw/NJS_Extract/Funs.lean','verifier.candidate.canonical_scan_loop0.body'),('verify_in_place','evidence/multiproof-20261107/NJA_emitted/raw/NHR_NJA_multiproof/Funs.lean','multiproof.verify_in_place_loop0.body')]
 for label,p,name in controls:
  s=g.text(p);m=re.search(r'(?m)^def '+re.escape(name)+r'\s',s);end=s.find('/--',m.end());body=s[m.start():end];tail=body.split('match o with',1)[1].split('| some ',1)[0]
  hits=sites('def tail_control : Unit :=\n'+tail)
  checks[label]={'path':p,'sha256':sha(g.read(p)),'definition':name,'normal_exhaustion_branch':tail.strip(),'tail_loss_hits':sum(len(d['done_none']) for d in hits),'pass':not any(d['done_none'] for d in hits),'raw_internal_candidate_count':sum(len(d['done_none']) for d in sites(s) if label in d['definition'])}
 a['controls'].update(checks)
 # The batch exit has no CLOSED ancestor in the authoritative conservative native graph.
 G=collections.defaultdict(set)
 for r in rows:G[r['function']].update(r['canonical_callees'])
 bad={r['function'] for r in rows if r['function'].endswith('::batch_tree')};last=set()
 while last!=bad:last=bad.copy();bad|={f for f,cs in G.items() if cs&bad}
 impact=[]
 for r in rows:
  if r['function'] in bad:
   impact.append({'row':r['row'],'status':r['status'],'function':r['function'],'verdict':'AFFECTED_PATH_ALREADY_OPEN','roots':r['root_owners'],'reason':'Native call graph reaches batch_tree with lost error Result; no CLOSED root claimed. Preserve OPEN; repair exact error transport.'})
  elif r['status']=='CLOSED':
   impact.append({'row':r['row'],'status':r['status'],'function':r['function'],'verdict':'INSENSITIVE_TO_BATCH_TREE_BY_CALL_GRAPH','roots':r['root_owners'],'reason':'No path to batch_tree in ledger19 canonical_callees conservative union. This graph-based nonconsumption check alone is not a full theorem-body dependency proof.'})
 a['impact_summary']={'closed_rows_reaching_batch_tree':sum(r['status']=='CLOSED' and r['function'] in bad for r in rows),'confirmed_mistranslated_native_function':'candidate::batch_tree','no_ledger_edit':True,'complete_audit':False}
 a['source_post_loop_reviews']=post_reviews
 a['coverage_limitations']=['Conservative source resolution keeps all tracked filename matches; it is not the exact selected source-to-olean map. Recorded object/import closure is pinned separately.','Missing source or tool-origin pins remain explicit; no-hit is not a general source-equivalence theorem.','Rows labelled INSENSITIVE_TO_BATCH_TREE_BY_CALL_GRAPH need no reopening for the known defect on that evidence alone; no claim of complete theorem-body nonconsumption audit.']
 P.joinpath('NKT_AUDIT.json').write_text(json.dumps(a,separators=(',',':'))+'\n')
 P.joinpath('NKT_REVIEWS.json').write_text(json.dumps(reviews,indent=2)+'\n')
 P.joinpath('NKT_ROW_IMPACT.json').write_text(json.dumps(impact,indent=1)+'\n')
 P.joinpath('NKT_SOURCE_SITES.json').write_text(json.dumps(post_reviews,indent=2)+'\n')
 print(json.dumps({'audited_occurrences':len(a['functions']),'manual_site_packets':len(reviews),'unreviewed_candidates':sum(x['verdict']=='UNREVIEWED_CANDIDATE' for x in reviews),'source_post_loop_shapes':len(post_reviews),'closed_reaching_batch_tree':a['impact_summary']['closed_rows_reaching_batch_tree'],'negative_controls':{k:v['pass'] for k,v in checks.items()},'wall_seconds':time.monotonic()-start}))
if __name__=='__main__':main()
