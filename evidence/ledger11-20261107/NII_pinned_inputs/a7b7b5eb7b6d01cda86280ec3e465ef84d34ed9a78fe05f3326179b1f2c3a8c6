#!/usr/bin/env python3
"""Additive gates over unchanged NFK admission; preserve ledger7 qualifications."""
from pathlib import Path
import sys,json,lzma,re,hashlib,importlib.util,subprocess,copy,collections
sys.dont_write_bytecode=True
E=Path(__file__).resolve().parent;R=E.parents[1]
sha=lambda b:hashlib.sha256(b).hexdigest()
J=lambda p:json.loads((E/p).read_text())
spec=importlib.util.spec_from_file_location('NGC_pinned_NFK',R/'evidence/ledger6-20261104/NFK_validate.py');NFK=importlib.util.module_from_spec(spec);spec.loader.exec_module(NFK)
raw=lzma.decompress((R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz').read_bytes());assert sha(raw)==(R/'evidence/ledger7-20261104/NFX_LEDGER.json.sha256').read_text().strip()
base=json.loads(raw);by={r['row']:r for r in base['rows']};NFK.BASE_CREDITS=base['NEZ_credits'];standard={'propext','Classical.choice','Quot.sound'}
KMX='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
assert sha((R/'evidence/kani-mitig-20261028/KMX_copy_stubs.patch').read_bytes())==KMX
limits={'memory.high':'6442450944','memory.max':'8589934592','memory.swap.max':'0','pids.max':'64'}
def receipt(a,status):
 r=J(a+'/receipt.json');ad=J(a+'-admission.json');assert r['exit_status']==status and ad['exit']==0 and ad['reservation']['allowed'] is True,a
 assert r['limits']==limits and int(r['swaps'])==0,a
 for n,h in r['source_hashes'].items():assert sha((E/a/'sources'/n).read_bytes())==h,(a,n)
 return r

def native(k,status):
 a=f'NGC_K{k:03}';r=receipt(a,status);g=J(a+'-graph-check.json');lock=J(a+'-lock-check.json');sc=J(a+'-source-check.json')
 assert g['graph_matches_frozen'] and lock['unchanged'] and lock['before']==lock['after']=='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef' and sc['errors']==[],a
 assert r['env']['CARGO_NET_OFFLINE']=='true' and r['env']['CARGO_PROFILE_DEV_OPT_LEVEL']=='3'
 text=(E/a/'stdout.log').read_text();assert 'VERIFICATION:- '+('FAILED' if status else 'SUCCESSFUL') in text,a
 if status:assert re.search(r'\*\* 1 of \d+ failed',text) and 'Failed Checks: assertion failed:' in text and 'unwinding assertion' not in text,a
 return r

def pair(p,n):
 a=native(p,0);b=native(n,1)
 explicit=p in [6,18,28,38,84]
 assert (a['module'].replace('_positive','_negative')==b['module']) if explicit else (a['module']==b['module'])
 aa={k:v for k,v in a['source_hashes'].items()if k.endswith('.rs')};bb={k:v for k,v in b['source_hashes'].items()if k.endswith('.rs')};assert aa==bb,(p,n)
 assert '--cfg NGC_invert' not in a['env']['RUSTFLAGS']
 assert ('--cfg NGC_invert' not in b['env']['RUSTFLAGS']) if explicit else ('--cfg NGC_invert' in b['env']['RUSTFLAGS'])
 return [f'NGC_K{p:03}',f'NGC_K{n:03}']

def parse(log):return [json.loads(l[len('NEP_RESULT '):])for l in log.splitlines()if l.startswith('NEP_RESULT ')]
def audit():
 receipt('NGC_L060',0);receipt('NGC_L061',0);receipt('NGC_L062',0);receipt('NGC_L063',1);receipt('NGC_L064',0);receipt('NGC_L066',0);receipt('NGC_L067',0);receipt('NGC_L068',0);receipt('NGC_L070',0)
 assert sha((E/'NGC_EXPECTED_IMPORTS.jsonl').read_bytes())==J('NGC_L070/receipt.json')['source_hashes']['NGC_EXPECTED_IMPORTS.jsonl']
 assert sha((E/'NGC_COMBINED_IMPORT.lean').read_bytes())in J('NGC_L066/receipt.json')['source_hashes'].values()
 result={}
 for n in range(9):
  rows=parse((E/'NGC_final_audit'/f'proof{n}.log').read_text());assert rows
  for x in rows:
   assert x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<=standard,x['root']
   result[x['root']]=x
 for x in parse((E/'NGC_final_audit/prestate.log').read_text()):
  assert x['equal'] and set(x['walked_axioms'])==set(x['collect_axioms'])<=standard
  result[x['root']]=x
 NFK.fixtures(parse((E/'NGC_final_audit/fixtures.log').read_text()))
 NFK.fixtures(parse((E/'NGC_final_audit/fixturesFinal.log').read_text()))
 assert set(J('NGC_AUDIT_ROOTS.json'))==set(result)
 loaded=[json.loads(l)for l in (E/'NGC_LOADED_scan.jsonl').read_text().splitlines()];assert all(r['imports_match'] and not r['dangling']for r in loaded)
 assert (E/'NGC_WALKER.lean').read_bytes()==(R/'evidence/axaudit2-20261102/NEP_WALKER.lean').read_bytes()
 return result,loaded
class Support:
 def support(self,c):
  for x in NFK.walk(c):
   if isinstance(x,dict) and {'path','sha256'}<=x.keys():assert sha((R/x['path']).read_bytes())==x['sha256'],x['path']
def pins(names):return [dict(path=str((E/n).relative_to(R)),sha256=sha((E/n).read_bytes()))for n in names]
def seal(c):c['semantic_review_sha256']=sha(json.dumps(c,sort_keys=True).encode());return c
V='crates/aspis-r1-cost-probe/src/verifier.rs::';H='crates/aspis-core/src/r0/heap.rs::filled';D='programs/r1-cost-probe/src/lib.rs::SolanaDigest::digest'
common='Retained P6/D188 option-A native semantic transport; frozen source/features and same carrier/ABI; compiler/library/allocator/cleanup/source-to-ELF realization. Reclassification, never premise removal.'
specs=[
 (H,['TX1:064','TX2:045'],'AspisR1.NGC_ReferenceValues.heap','Frozen-reachable u8, QM31, [u64;4], WideExact; n<=32768; effect-free identity Clone checked per monomorph; same actual reservation Result; allocation failure/abort and owned carrier effects retain their pinned Std realization.',[(20,21),(22,23),(24,25),(26,27),(28,29)]+[(p,p+1)for p in range(42,66,2)]+[(p,p+1)for p in range(74,82,2)]+[(p,p+1)for p in range(86,94,2)]+[(100,31),(32,33),(34,35),(67,68)],'NGC_ReferenceValues.lean'),
 (V+'Accumulator::new',['TX1:174'],'AspisR1.NGC_Initialization.constructor','S2, the sole frozen TX1 constructor call; final_len=64; SAME full heap Result and allocation; success zero64/rhs0/power1/next0, failure Allocation.',[(4,5),(6,7),(94,95)],'NGC_Initialization.lean'),
 (D,['TX1:327','TX2:210'],'AspisR1.NGC_DigestBridge.forwarding','SAME ordered borrowed input descriptors, 0..9 parts each length<=57607, duplicates/empty parts allowed; arbitrary full32-byte syscall reply; wrapper returns unchanged, immutable inputs. SHA value=H remains RuntimeSha256Value.',[(82,83),(84,85)],'NGC_DigestBridge.lean'),
 (V+'BatchedWeights::value',['TX1:178'],'AspisR1.NGC_ValueBridge.value','SAME64 arbitrary full-u64 raw rows and index<64; exact four natural residues modulo2147483647; no bound on raw limbs besides u64.',[(14,15),(18,19)],'NGC_ValueBridge.lean'),
 (V+'BatchedWeights::finish',['TX1:175'],'AspisR1.NGC_FinishContents.contents','SAME pending and mutable weights pair in NFS_QueryInvariant.Domain p start finish a b; both lengths64. Exact output map(raw%P), canonical limbs; rhs/power/next unchanged; native one arbitrary cursor/write/frame plus fixed64 control and Lean induction.',[(12,13),(14,15),(16,17),(18,19)],'NGC_FinishContents.lean')]
def build():
 audited,loaded=audit();closed=[];candidates={};certs={};edges=[]
 for p,n in [(36,37),(38,39),(40,41)]:pair(p,n)
 assert J('NGC_WINDOW_ASSOCIATION.json')['status']=='PASS'
 assert J('NGC_WINDOW_ASSOCIATION.json')['native_input_sha256']==sha((E/'NGC_NATIVE_INPUTS.json').read_bytes())
 assert J('NGC_SOURCE_ASSOCIATION.json')['status']=='PASS'
 assert J('NGC_SOURCE_ASSOCIATION.json')['native_input_sha256']==sha((E/'NGC_NATIVE_INPUTS.json').read_bytes())
 for f,ids,root,domain,ps,source in specs:
  native_ids=[a for p,n in ps for a in pair(p,n)];assert root in audited
  matches=[]
  for p in E.glob('NGC_L???/receipt.json'):
   r=json.loads(p.read_text())
   if r['exit_status']==0 and sha((E/source).read_bytes())in r['source_hashes'].values():matches.append(str(p.relative_to(E)))
  assert matches,source
  children=[]
  for callee in by[ids[0]]['canonical_callees']:
   reason={H:'Literal S2 final_len64, exact zeroK, full owned Result and allocation error; instantiated extracted filled law.',V+'BatchedWeights::value':'Each enumerate index<64 from SAME mutable64 allocation; raw64 same object. Exact residue output and frame from NGC_ValueBridge.value.', 'crates/aspis-core/src/field.rs::M31::reduce_u64':'Four actual same-row u64 values; closed reducer domain is all u64, no overflow-bound premise.', 'crates/aspis-r1-cost-probe/src/transport.rs::Variant::final_len':'Literal S2 matches closed pure Variant theorem returning64.'}[callee]
   e=dict(edge=f+' -> '+callee,status='CLOSED',certificate=dict(native=native_ids,lean_root=root,domain_proof=reason));edges.append(e);children.append(e)
  cc=dict(function=f,rows=ids,status='CLOSED',form='ruling (y) hybrid with native windows and explicit retained realization',domain=domain,native=native_ids,lean_root=root,axioms=audited[root]['walked_axioms'],internal_edges=children,KMX_patch_sha256=KMX,physical_interpretation=common,inner_hypotheses_remaining=[])
  closed.append(cc)
  for rid in ids:
   row=by[rid];frozen=subprocess.check_output(['git','show',base['frozen_revision']+':'+row['source_file']],cwd=R);start,end=row['frozen_body_byte_range'];assert sha(frozen[start:end])==row['frozen_body_sha256']
   # Per-run full frozen-file gates bind reached unmodified heap; local fission verified by exact erasure.
   support=[source,'NGC_SOURCE_ASSOCIATION.json','NGC_WINDOW_ASSOCIATION.json','LPh_STUBS.md','NGC_COMBINED_IMPORT.lean','NGC_AUDIT_ROOTS.json']+[a+'/'+n for a in native_ids for n in ['receipt.json','stdout.log']]
   cert=seal(dict(id='NGC::'+rid,row=rid,subject=f,function=f,frozen_body_sha256=row['frozen_body_sha256'],domain=domain,top_hypotheses=[common],inner_hypotheses_remaining=[],native=cc,external_obligations={o['id']:dict(classification='Exact native call-window/same-state argument schedule plus paired extracted/adopted value/frame laws; retained std/runtime realization at the named physical boundary',detail=o['call'])for o in row['caller_domain_obligations']if 'callee'not in o},support=pins(support)))
   NFK.certificate_checks(Support(),cert);candidate=NFK.materialize_recipe(row,cert,'NGC',{'edges':edges})
   for ob in candidate['caller_domain_obligations']:
    if ob.get('callee')in[H,V+'BatchedWeights::value']:ob['callee_claims']=['NGC::'+ob['callee']]
   assert not NFK.row_checks(candidate,row,cert)
   candidates[rid]=('NGC',candidate);certs[rid]=cert
 out=NFK.admit(base,candidates,certs,{'NGC':sorted(candidates)})
 outby={r['row']:r for r in out['rows']};assert all(outby[r]['composed_status']=='CLOSED'for r in candidates)
 for r in base['rows']:
  if r['row']not in candidates:assert outby[r['row']]['composed_status']==r['composed_status'],r['row']
 tests=[];rid=next(iter(candidates));candidate=candidates[rid][1];cert=certs[rid]
 for name,mutate in [('body hash',lambda x:x.update(frozen_body_sha256='0'*64)),('undischarged hypothesis',lambda x:x['named_hypotheses'][0].update(discharged_by=None)),('open dependency',lambda x:x.update(open_transitive_dependencies=['missing'])),('missing selected claim',lambda x:x.update(selected_claims=[]))]:
  bad=copy.deepcopy(candidate);mutate(bad);assert NFK.row_checks(bad,by[rid],cert);tests.append(name)
 for name,mutate in [('certificate seal',lambda c:c.update(domain='changed')),('residual inner hypothesis',lambda c:c.update(inner_hypotheses_remaining=['open']))]:
  bad=copy.deepcopy(cert);mutate(bad)
  try:NFK.certificate_checks(Support(),bad)
  except(ValueError,AssertionError):tests.append(name)
  else:raise AssertionError(name)
 def put(n,x):(E/n).write_text(json.dumps(x,indent=1)+'\n')
 raw=json.dumps(out,indent=1).encode();(E/'NGC_COMPOSED_LEDGER.json.xz').write_bytes(lzma.compress(raw));(E/'NGC_COMPOSED_LEDGER.json.sha256').write_text(sha(raw)+'\n')
 put('NGC_CERTIFICATES.json',certs);put('NGC_EDGES.json',edges)
 put('NGC_CLOSED.json',dict(frozen_revision=base['frozen_revision'],new_composed_functions=len(closed),new_composed_rows=len(candidates),driver_root_status='OPEN',functions=closed,reused_writer_rows='NFT revalidated; no new occurrence invented or counted; NFX S qualifiers preserved'))
 counts=dict(collections.Counter(r['composed_status']for r in out['rows']))
 put('NGC_LEDGER_DELTA.json',dict(baseline='evidence/ledger7-20261104/NFX_LEDGER.json.xz',baseline_sha256=sha(lzma.decompress((R/'evidence/ledger7-20261104/NFX_LEDGER.json.xz').read_bytes())),newly_closed=sorted(candidates),new_functions=len(closed),new_rows=len(candidates),counts_after=counts,unchanged_other_statuses=True,validator='unchanged NFK.certificate_checks/materialize_recipe/row_checks/admit with additive native/source/domain/copy/ax2 gates',checkpoint='TX1:186 OPEN; preparation provenance and native pending-constructor/source-prefix binding remain explicit boundaries',target_established=False))
 put('NGC_AUDIT.json',dict(status='PASS',combined_import='NGC_L066',raw_batches=['NGC_L062','NGC_L063','NGC_L068'],local_checkpoint_native_pairs=[[36,37],[38,39],[40,41]],final_scan='NGC_L070',initial_scan_repair='NGC_L063 raw batches green; source-backed expected header repair in NGC_FINAL_SCAN_REPAIR.json; focused scan L064 then new-prestate combined scan L068',root_count=len(audited),roots=audited,fixtures=parse((E/'NGC_final_audit/fixtures.log').read_text()),standard_axioms_only=True,zero_dangling=True,module_count=len(loaded),walker_sha256=sha((E/'NGC_WALKER.lean').read_bytes()),unchanged_NFK_validator_sha256=sha((R/'evidence/ledger6-20261104/NFK_validate.py').read_bytes()),mutation_tests=tests,retained_trust=[common,'RuntimeSha256Value: SHA256=H','RuntimePersistence','RuntimeReturnData accepted nonempty1..1024','RuntimeMemcmp accepted'],added_trust=[],removed_trust=[],cold_release_replay=False))
 print(json.dumps(dict(valid=True,new_functions=len(closed),new_rows=len(candidates),counts=counts,raw_roots=len(audited),modules=len(loaded))))
if __name__=='__main__':build()
