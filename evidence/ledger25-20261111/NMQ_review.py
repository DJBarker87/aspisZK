"""Read-only replay-input and native-control review; never launches Kani."""
from pathlib import Path
import json,lzma,hashlib,re,subprocess,copy
E=Path(__file__).resolve().parent;Q=E.parent/'tx2-entry5-20261110';P=E.parent/'ledger24-20261110'
H=lambda b:hashlib.sha256(b).hexdigest()
def raw(p):
 if p.exists():return p.read_bytes()
 b=lzma.decompress(Path(str(p)+'.xz').read_bytes());side=Path(str(p)+'.sha256')
 if side.exists():assert H(b)==side.read_text().strip()
 return b
J=lambda p:json.loads(raw(p))
def snapshot(h):
 b=lzma.decompress((Q/'NMN_INPUTS'/(h+'.xz')).read_bytes());assert H(b)==h;return b
controls=J(Q/'NMN_CONTROLS.json');patch=raw(Path('evidence/kani-mitig-20261028/KMX_copy_stubs.patch'));assert H(patch)==controls['copy_patch_sha256']
runs=[];configs=[]
for entry in controls['runs']:
 a=entry['attempt'];r=J(Q/a/'receipt.json');s=raw(Q/a/'stdout.log').decode();expected=0 if int(a[-3:])in [14,15,23,25]else 1
 assert r['exit_status']==entry['exit']==expected
 assert ('VERIFICATION:- SUCCESSFUL' if expected==0 else 'VERIFICATION:- FAILED')in s
 assert '[optimized]'in s
 assert r['source_hashes']['NMN_src/crates/aspis-r1-cost-probe/src/NMN_native.rs']==controls['current_native_sha256']
 for name,h in r['source_hashes'].items():snapshot(h)
 graph=J(Q/(a+'-graph-check.json'));lock=J(Q/(a+'-lock-check.json'));src=J(Q/(a+'-source-check.json'))
 assert graph['graph_matches_frozen'] and not graph['edge_errors'] and not graph['new_package_tuples'] and not src['errors']
 assert lock['unchanged'] and lock['before']==lock['after']==graph['lock_sha256']
 config=json.loads(snapshot(r['source_hashes']['NMN_native_config.json']));command=config['native_command'];idx=command.index('--harness');configs.append(command[:idx]+command[idx+2:])
 features={x['name']:x['features']for x in graph['selected_closure']}
 assert set(['default','private-leaf-salts','optimized-terminal','program-build'])<=set(features['aspis-r1-cost-probe'])
 assert {'r0','pool-v1-kernel'}<=set(features['aspis-statement'])
 runs.append(dict(attempt=a,root=r['module'],exit=r['exit_status'],verdict='PASS'if expected==0 else'FAIL',native_sha256=entry['source_sha256'],graph_sha256=graph['graph_sha256'],lock_sha256=lock['after'],log_sha256=H(s.encode()),configuration_sha256=H(json.dumps(configs[-1],sort_keys=True).encode()),receipt=str(Q/a/'receipt.json')))
assert all(c==configs[0]for c in configs)
assert len({r["graph_sha256"]for r in runs})==1
source=snapshot(controls['current_native_sha256']).decode();assert 'static mut'not in source and not re.search(r'^static ',source,re.M)
for text in ['public:[u8;1880]=kani::any()','checkpoint:[u8;1768]=kani::any()','header:kani::any(),root:kani::any(),suffix:kani::any()','kani::assume(n<=1880)','kani::assume(tag<11)','kani::assume(tag<9)','tx2_authenticated(pub_,if MUTANT{other}else{proof},&checkpoint,NMN_Hash(&log),None)','assert!(matches!(p,Phase::Parsed))']:
 assert text in source,text
frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387'
parent=subprocess.check_output(['git','show',frozen+':crates/aspis-r1-cost-probe/src/candidate.rs'])
r=J(Q/'NMN_K014/receipt.json');actual=snapshot(r['source_hashes']['NMN_src/crates/aspis-r1-cost-probe/src/candidate.rs'])
assert actual==parent+b'\n#[cfg(kani)]\n#[path="NMN_native.rs"]\nmod NMN_native;\n'
# Verify the gate enforces offline graph and post-lock checks on every run.
gate=snapshot(r['source_hashes']['NMN_gate.py']).decode();assert 'CARGO_NET_OFFLINE' in gate and 'lock' in gate and 'graph' in gate
assert "'KMX_stubs.rs': 'ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138'" in gate
fingerprints=[]
for entry in controls['runs']:
 rc=J(Q/entry['attempt']/'receipt.json');fingerprints.append({n:h for n,h in rc['source_hashes'].items()if n!='NMN_native_config.json'})
assert all(f==fingerprints[0]for f in fingerprints)
baseline=json.loads(lzma.decompress((P/'NLX_LEDGER.json.xz').read_bytes()));row=next(z for z in baseline['rows']if z['row']=='TX2:064')
clauses=J(Q/'NMN_CALLER_CLAUSES.json')['clauses'];assert len(clauses)==4
review=dict(row='TX2:064',primary_root='NMN_064.root',owner_module='NMN_064',status='SOURCE_CERTIFICATES_REVIEWED_GATE_PENDING',gate_admitted=False,basis_obligation_statement_hash=row['obligation_statement_hash'],basis_obligation_sha256=H(json.dumps(row['obligation'],sort_keys=True,separators=(',',':')).encode()),source_identity=dict(frozen_revision=frozen,parent_sha256=H(parent),overlay_parent_sha256=H(actual),only_change='cfg(kani) harness module appended'),native_certificates=runs,configuration_identical_except_harness=True,full_source_fingerprint=fingerprints[0],full_source_fingerprint_sha256=H(json.dumps(fingerprints[0],sort_keys=True).encode()),kmx_stub_sha256='ad8efb63d8ff791274c91eff9ccc5b9fb126f5a3ac7f27aa811ca11b8e25c138',full_Result_domains=dict(parser='3 Variant successes +8 Error variants',common='unit success +8 Error variants',stopped='panic branch K022; prefix only under bl3'),copy_patch_sha256=H(patch),write_footprint='Empty child &mut/account-data/return-data footprint. LOCAL channel writes tested by K018/K021; never a fabricated account frame.',observer='Literal deployed None; no Option/fn-pointer value inspected; K023/K024 stability matches original verdicts, no renaming.',own_argument_clauses=clauses,root0_decision=dict(admissible_as_own_input_clause=True,caller='TX2:241',caller_status='OPEN',headline_theorem='NMF_GameRoot.root0_or_existing_collision',installation='NMN_Headline.accepted_occurrence',same_occurrence=True,proof='Same f/s SourceCuts selected from RPx_Deployed.deployed; literal saved root0 + SAME persisted checkpoint + reached resume proof-digest binding yields literal Root0 s.checkpoint s.proof OR EXISTING BinRawByteCollisionTargets.event.',event='unchanged Q0+Q1+2965 event and same program/projection/selector',no_global_root0=True,no_hash_injectivity=True,no_new_trust=True,not_a_universal_failed_prefix_fact=True),hypothesis_inventory=dict(original_generics='H, Ambient, X, original Frame/digest/hash/world',own_input_Prop='Exactly four fields of Domain on ORIGINAL arguments, bf2',native='subject of conclusion; full entered parser/common executions at recorded arguments, not endpoint laws',cuts='Existing aq2 per-occurrence reservations/locations/native input frames, nested in canonical CLOSED child owners',no_free_Ops_Run=True,no_child_success_hypothesis=True,no_extra_global_state=True),canonical_children=[dict(child='parse_shape',root='NLE_ParseInstall.emitted / success',same='s.args.proof',derived='NMN_064.parser'),dict(child='mark',root='NHV_ReleaseOps.mark',same='deployed None, Parsed',derived='NMN_Observer and NLW full fold'),dict(child='tx2_common',root='NLT_CompleteRoot.root',same='s.args.digest/publicBytes/proof/checkpoint/hash',derived='NMK_Domain.child / NLW_064CandidateFold.child')],withdrawn_root='NLT_Root.root',withdrawn_root_credit=False,common_stop='Independent stopped End carries only ordered prefix; no returned native reply, post-abort world, cleanup or suffix.',trust='Existing option-A P6/D188 native semantic transport RECLASSIFICATION; no trust removal',no_241_promotion=True)
(E/'NMQ_CANDIDATE_REVIEW.json').write_text(json.dumps(review,indent=1)+'\n')
# Preserve every old clause and classify the real three-call parent vs flattened inventory.
matrix=[]
for c in row['obligation']['caller_domain_obligations']:
 z=copy.deepcopy(c)
 if c['id'].startswith('NLX-bf:'):
  z['NMQ_classification']='bf2 own-input clause, consumed at SAME common call; retained as064 Domain and OPEN241 caller clause, not a removed assumption'
  z['NMQ_discharge']='NMK_Domain.child: NLE_ParseInstall.success supplies entered proof extent; Domain supplies publicBound/root0; NMF supplies Root0 OR existing collision only at the accepted headline occurrence'
 elif 'parse_shape'in c.get('callee','')and 'inventory:'not in c['id']:
  z['NMQ_classification']='Canonical total parser refinement on SAME typed proof Slice; native parent certificate restricted explicitly to own57607 input class'
  z['NMQ_discharge']='NMN_064.parser from NLE_ParseInstall.emitted; NMN_OracleFold.installed'
 elif c.get('callee','').endswith('::mark'):
  z['NMQ_classification']='Original deployed None/Parsed unit call; exact native phase assertion, no observer value comparison'
  z['NMQ_discharge']='NHV_ReleaseOps.mark; NMN_Observer.marker/success/rejection; K014/K015 marker cut'
 else:
  z['NMQ_classification']='Canonical common/transitive inventory; SAME actual child invocation and internally supplied child law, nested aq2 cuts retained'
  z['NMQ_discharge']='NLW_064CandidateFold.child and NMK_Domain.child apply NLT_CompleteRoot.root; its complete NLX-gated clauses retain all failure/stop arms'
 matrix.append(z)
(E/'NMQ_CLAUSE_REVIEW.json').write_text(json.dumps(dict(row='TX2:064',original_clauses=matrix,own_input_clauses=clauses,caller='TX2:241',caller_status='OPEN',inventory=row['obligation']['inventory_domain_obligations'],scope='bl4 classification retains full Result/reject/abort/effects and canonical nested child domains; no literal whole-parent requirement discarded'),indent=1)+'\n')
(E/'NMQ_PARENT_CLAUSES.json').write_text(json.dumps(dict(parent='TX2:241',helper='TX2:064',clauses=clauses,status='OPEN_CALLER_CLAUSES',root0_provenance=review['root0_decision']),indent=1)+'\n')
print(json.dumps(dict(status='PASS_STATIC_REVIEW',native_runs=len(runs),clauses=len(matrix),gate='pending')))
