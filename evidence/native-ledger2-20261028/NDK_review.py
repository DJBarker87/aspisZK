"""Reviewed current-head associations layered into the NCZ reconstruction.

Machine checks verify explicit assertions and pins, not arbitrary prose semantics.
No compiler, solver, host job, source rewrite, or native tool adoption occurs.
"""
import collections
import hashlib
import json
from pathlib import Path
import re

HERE=Path(__file__).resolve().parent
OLD='evidence/native-compledger-20261028/'
LOCK='5782e6a32026fdd95d252d0db7ea20b16716e6deb4f5a397e744886bb6ba22ef'
OPTIMIZED={'pool-v1-pair-forest-endpoint-selector-cache-audit', 'pool-v1-pair-forest-copy-pattern-basis-audit', 'pool-v1-pair-forest-semantic-factor-audit', 'pool-v1-pair-forest-copy-finish-dot-basis-audit', 'pool-v1-pair-forest-copy-selector-tensor-basis-audit', 'pool-v1-pair-forest-packed-digest-audit', 'pool-v1-pair-forest-packed-range-audit', 'pool-v1-pair-forest-pattern-window-audit', 'pool-v1-pair-forest-active-mask-basis-audit', 'pool-v1-pair-forest-copy-tag-dot-basis-audit', 'pool-v1-pair-forest-binary-copy-weights-audit', 'pool-v1-pair-forest-packed-digest-selector-tensor-audit'}
PATCH='bcdf749b78eb6143789500d98d64ec3d407b8a17a6d1290c70c822473e8e9a67'
sha=lambda b:hashlib.sha256(b).hexdigest()


def check_features(g, scope):
    assert g['graph_matches_frozen'] is True and not g['edge_errors']
    assert g['lock_sha256']==LOCK
    all_features=g.get('resolved_features_all_crates',g.get('all_crate_features'))
    assert all_features and len(all_features)>=400, 'missing all-crate resolved feature list'
    fs=({k:set(v) for k,v in all_features.items()} if isinstance(all_features,dict)
        else {v['name']:set(v['features']) for v in all_features})
    reached={v['name']:set(v['features']) for v in g['selected_closure']}
    assert {'r0'}<=fs['aspis-core']
    assert {'r0','pool-v1-kernel'}<=fs['aspis-statement']
    audits={f for f in fs['aspis-statement'] if f.endswith('-audit')}
    assert audits==OPTIMIZED, 'optimized statement expansion missing or changed'
    assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=fs['aspis-r1-cost-probe']
    if scope=='program':
        assert {'pool-adapter','private-leaf-salts'}<=reached['aspis-r1-cost-probe-program']
        assert 'no-entrypoint' not in reached['aspis-r1-cost-probe-program']
    else:
        assert scope in ['core-helper','library-helper'], 'unrecorded helper scope'
        # Only the core or library helper is the proof target. No program root,
        # no-entrypoint, ELF, or whole-program deployment claim is made.
        if scope=='library-helper':
            assert {'default','private-leaf-salts','optimized-terminal','program-build'}<=reached['aspis-r1-cost-probe']
    return {'scope':scope,'all_crates_recorded':len(all_features),
            'statement_optimized_features':sorted(audits),
            'reached_project_features':{k:sorted(v) for k,v in reached.items() if k.startswith('aspis-')}}


def check_native(receipt, log, positive):
    assert receipt['exit_status']==(0 if positive else 1), 'native exit/control mismatch'
    assert 'Checking harness ' in log and 'Failed to match' not in log
    assert 'timed out' not in log.lower() and 'unwinding assertion' not in log.lower()
    assert ('VERIFICATION:- SUCCESSFUL' if positive else 'VERIFICATION:- FAILED') in log
    failures=re.findall(r'\*\* (\d+) of \d+ failed',log)
    assert failures and failures[-1]==('0' if positive else '1'), 'control not a unique semantic failure'
    assert '1 total.' in log, 'expected one exact selected harness'
    if not positive:
        assert 'Failed Checks:' in log
    assert receipt['copy_patch_sha256']==PATCH
    command=receipt.get('native_command',[])
    assert '--exact' in command and '--harness' in command


def check_theorem(receipt, theorem, source, current):
    assert receipt['exit_status']==0, 'failed Lean attempt earns no credit'
    assert source==current, 'passing source differs from selected theorem source'
    lines=receipt['print_axioms']
    assert lines and not any('sorryAx' in str(x) for x in lines)
    matches=[l for l in lines if "'"+theorem+"'" in l]
    assert len(matches)==1, ('missing exact theorem axiom audit',theorem)
    for line in lines:
        if 'axioms:' in line:
            names=line.split('axioms:',1)[1].strip().strip('[]').replace('\n','').split(',')
            assert all(n.strip() in ['propext','Classical.choice','Quot.sound',''] for n in names),line
    assert re.search(r'\btheorem\s+'+re.escape(theorem.split('.')[-1])+r'\b',current.decode())


def refresh_claims(s, functions, claims):
    specs=json.loads((HERE/'NDK_ASSOCIATIONS.json').read_text())
    decisions=[]
    def packet_files(directory):
        # Pin current packet statements, source audits, extraction/tool pins and
        # aggregate results; exclude lane copies of the old derived ledger.
        return sorted(p for p in s.tree if p.startswith(directory) and
            '/' not in p[len(directory):] and
            (p.endswith('.md') or any(x in Path(p).name for x in ['EXTRACTION_PINS','SOURCE_AUDIT','FROZEN_SOURCE_AUDIT','ACCEPTED_MODULES','FINAL_AUDIT','VALIDATION','LEDGER_DELTA','FEATURE_SUPPLEMENT'])) and
            s.tree[p][1]<2*1024*1024)
    for spec in specs:
        directory='evidence/'+spec['packet']+'/'
        row=s.obj(spec['delta'])[spec['delta_key']][spec['index']]
        assert (row if isinstance(row,str) else row['function'])==spec['function']
        if spec['admit']:
            check_delta_association(spec,row)
            assert row.get('status',row.get('local_status')) in ['CLOSED-local','CLOSED-CONDITIONAL']
            assert spec['domain']==row['domain']
        name=spec['function']; assert name in functions,name
        ev=packet_files(directory);rs=[];features=[];theorems=[]
        for p in ev:s.read(p)
        for item in spec['native']:
            a=item['attempt']; p=directory+a+'/receipt.json';r=s.obj(p);rs.append(p)
            log=s.text(directory+a+'/stdout.log')
            check_native(r,log,item['positive'])
            manifest=r['native_command'][r['native_command'].index('--manifest-path')+1]
            expected_manifest={'core-helper':'crates/aspis-core/Cargo.toml','library-helper':'crates/aspis-r1-cost-probe/Cargo.toml','program':'programs/r1-cost-probe/Cargo.toml'}[spec['feature_scope']]
            assert manifest.endswith(expected_manifest), 'proof target/feature scope mismatch'
            g=s.obj(directory+a+'-graph-check.json')
            features.append(dict(attempt=a,**check_features(g,spec['feature_scope'])))
            lock=s.obj(directory+a+'-lock-check.json')
            assert lock['unchanged'] and lock['before']==lock['after']==LOCK
            assert not s.obj(directory+a+'-source-check.json')['errors']
            # Exact archived receipt inputs, including negative configurations.
            for src,h in r['source_hashes'].items():
                q=directory+a+'/sources/'+src
                if q in s.tree:
                    assert sha(s.read(q))==h,('native receipt source hash',q)
                    ev.append(q)
            for q in s.tree:
                if q.startswith(directory+a+'/') and s.tree[q][1]<20*1024*1024:
                    s.read(q);ev.append(q)
            ev += [directory+a+'-graph-check.json',directory+a+'-lock-check.json',directory+a+'-source-check.json']
        for item in spec['theorems']:
            a=item['attempt'];p=directory+a+'/receipt.json';r=s.obj(p);rs.append(p)
            mod=item['name'].split('.')[0]
            source_path=directory+mod+'.lean'
            current=s.read(source_path)
            matches=[(k,h) for k,h in r['source_hashes'].items() if k.endswith('/'+mod+'.lean') or k==mod+'.lean']
            assert len(matches)==1,(a,mod)
            src,h=matches[0];q=directory+a+'/sources/'+src
            archived=s.read(q);assert sha(archived)==h
            check_theorem(r,item['name'],archived,current)
            log_path=directory+a+'/stdout.log';log=s.text(log_path)
            assert 'sorryAx' not in log and not re.search(r'\berror:',log)
            # Preserve complete statements, hidden callback qualifications and
            # carrier conversions in the pinned source rather than theorem names.
            theorems.append(dict(name=item['name'],source=source_path,source_sha256=sha(current),receipt=p,source_snapshot=q))
            ev += [source_path,q,log_path]
        admitted=spec['admit']
        if admitted:
            assert spec['rule14_dependencies'] and spec['native'] and theorems
            assert any(x['positive'] for x in spec['native']) and any(not x['positive'] for x in spec['native'])
        cid=spec['id']
        conditions=[dict(name=cid+'.PacketDomain',statement=spec['domain'],discharged_by=None),
                    dict(name=cid+'.PhysicalInterpretation',statement='Same native/cohort carrier, pinned source/reference/extraction and approved P6/D188 semantic transport; Rust ABI/library/allocator and installed dictionary/call transport remain explicit. '+spec['remaining'],discharged_by=None)]
        if admitted and spec['function'].endswith('::readonly_meta_ok'):
            conditions.append(dict(name=cid+'.Comparison',statement='Retained op36 comparison on these same Pubkeys equals native byte comparison (NDG_MetadataBridge.metadata premise).',discharged_by=None))
        if admitted and spec['function'].endswith(('::pool_program_id','::registry_program_id')):
            conditions.append(dict(name=cid+'.Installation',statement='Exact represented op45/op46 selection equals the actual headline dictionary; pool_slot/registry_slot only prove the reference installation selection.',discharged_by=None))
        c=dict(claim_id=cid,audit_id=cid,reported_status=row.get('status',row.get('local_status','OPEN')) if isinstance(row,dict) else 'OPEN',medium='Pinned safe reference + extraction + Lean cohort equation + controlled native body' if admitted else 'Partial/model evidence; no new local bridge',feature_parity='DEPLOYED features checked on each selected helper/program receipt' if admitted else 'UNDETERMINED for an enclosing bridge',profile=spec['feature_scope'],source_claim_text=[spec['domain'],spec['remaining']],evidence=sorted(set(ev+rs)),receipts=sorted(set(rs)),quarantined_support=[],replaced_quarantined_support=[],stub_attributes=[],arithmetic_stubs=[],admissible_local_credit=admitted,limitations=[] if admitted else [spec['remaining']],named_hypotheses=conditions,composition_trust='Owner amendment fifth P6/D188 reclassification, never removal',theorem_associations=theorems,native_feature_checks=features,rule14_dependency_audit=spec['rule14_dependencies'],delta_row=row)
        claims.setdefault(name,[]).append(c)
        decisions.append(dict(claim_id=cid,function=name,decision='ADMIT LOCAL CONDITIONAL' if admitted else 'REJECT STATUS PROMOTION',domain=spec['domain'],reason=spec['remaining'],evidence=spec['delta']))
    packets=review_packets(s)
    baseline=s.obj(OLD+'NCZ_LEDGER.json')
    # Pin inherited algorithm and association recipes as part of the refresh.
    s.read(OLD+'NCZ_validate.py');s.read(OLD+'NCZ_tests.py');s.read(OLD+'NCZ_SUPPLEMENTAL.json')
    return dict(previous_snapshot_revision=baseline['baseline_revision'],previous_coverage=baseline['coverage'],previous_frontier_size=len(baseline['critical_path']['frontier']),associations_sha256=sha((HERE/'NDK_ASSOCIATIONS.json').read_bytes()),decisions=decisions,packet_reviews=packets,other_merged_frontier_deltas=[p for p in s.tree if re.search(r'/(NDE|NDH|NDI)_',p)],quarantine_lift=False,trust_change='None; inherited reclassification retained',current_native_headline='target not yet established')


def review_packets(s):
    records=[
      ('native-decref-20261028','NCV','Primary op48/op49/op50 reference representations and slot selections are model results. Identity144 and policy predicates remain components; full native decoders and SDK caller association OPEN.'),
      ('native-decref2-20261028','NCX','Current-format op33/op34 extracted bodies, lossless carriers, installations and complete fixture observations established. Restricted rejection/windows/status/zero/validator checks do not close native op33/op34; all accepted and remaining error classes, record/SDK association OPEN.'),
      ('native-decnat-20261028','NDB','22 control-paired native component gates and primary reference window/loop/rejection laws. Full native op48/op49/op50 remains OPEN: original-wrapper same-input/context/Box/frame and complete model outcome assembly absent. Exclude memcmp unwind failures, K013 unpaired with stalled K014, failed Lean drafts.'),
      ('kani-k2leaf-20261028','KNF','Reused static local-leaf replacement support and exact feature/body audit already present in NCZ. Does not lift historical Option<fn> quarantine.'),
      ('kani-undet-20261028','KNG','Reused 23 re-established property associations and parity receipts already present in NCZ. No extra coverage credit for counting the replacement twice; old quarantined receipts remain excluded.'),
      ('native-tx2r2-20261028','NCN','U10/U11 remain OPEN. Local valid64-row value helper improves NCI one-row domain; raw windows and iteration cuts are partial. NCN_K061 graph has no per-crate feature selection or independently associated reached-body parity for this new domain, so no additional deployed credit. Existing NCS/KNG-qualified NCI credit retained. K077 unpaired gives none.'),
      ('native-tx2w-20261028','NCJ','U12/U13 remain OPEN. Guard/double/native iteration and sparse windows plus exact model arithmetic/Horner laws do not instantiate complete caller/loop/carrier/frame or free op ports. Whole finish_relation observer route retains K-2; no credit from pointer-dependent observations.'),
      ('native-tx2top-20261028','NCK','Typed model owned/SDK/authentication composition, loops and accepted-domain coupling are established. Full native U15/U16, actual lower bridges, allocated carriers and same-SDK dispatch remain OPEN. Model free op11/op51/op52 laws cannot be inferred from types.'),
      ('native-batchsk2-20261028','NCM','Stage1 complete CONDITIONAL TX1 batch/TX2 U09 composition with 18 native-step hypotheses. Stage2 has paired helper windows; none instantiates all 18 source cutpoint families. Whole batch/U09 OPEN; no new deployment credit from graph-only package/edge receipt lacking all-crate feature/body association. batch_key_at independently admitted through NDF.'),
      ('native-drvdom-20261028','NCT','Accepted-cut model domain derives weights64/next10/canonical weights and same-call leaf, retaining S2,22 bounds,nine nonweight groups. Accepted-run quantifiers do not cover failed/diverging writers. Superseded in scope by NCU prefix factorization, not erased.'),
      ('native-drvdom2-20261028','NCU','All-outcome model factorization and actual pre-writer prefix cover reached writers including fail/div. Same-prefix leaf retains S2,22 bounds,nine canonical groups plus local append/oracle/trace laws. Native reachability and source/ELF association remain OPEN.'),
      ('native-drvdom3-20261028','NDA','Same-prefix S2, all22 query bounds and distinctness, gamma/kappa/alpha/rho/semanticAlpha/claim canonicality established. domain_iff/remaining_iff reduce original domain EXACTLY to coordinates,rhs,power on that SAME cut. leaf retains those three groups or concrete primitive laws, plus unchanged local append/digest/oracle premises. Free-slot obstructions prevent silent concrete instantiation; native DriverEstablishedDomain remains OPEN.'),
      ('native-cpilot2-20261028','NCP','DigestDecode/canonicality/exact8,32 local witnesses retained as existing supplemental claims, without added deployed credit: graph summaries contain no exact per-crate feature association. Caller U03/U05 and encoder loops/validator remain OPEN; timeout/ICE/Vec substitution failures excluded.'),
      ('kani-sandbox-20261028','KNH','Kani0.68 candidate NOT adopted. K-1 false passes and K-2 name-sensitive verdicts persist, slice/Vec substitution unsupported, comparison incomplete and19 graph preflights missing. Tool probes give zero native/deployed credit; rule14 unchanged.'),
      ('native-elfpins-20261028','NCY','Fresh devnet/Pool SBF artifact reproduction; default reused from NCR. No logical/native bridge closed; P7 and L188 source/feature/domain/final release audit remain. Artifact reproduction is not semantic correspondence.'),
      ('native-sbfstack-20261028','NDC','Exact warned mangled instances omitted from linked final ELFs; no new P7 qualification recommended for those warnings. Omission is not fail-closed, whole runtime safety, indirect-call proof, privacy or native correspondence.'),
      ('joint-tx2fix3-20261028','JHv','Current-format registry authentication seventh child and SAME SDK validation composed, conditional on FixturePdaRuntime. Initial wrapper aggregation failed at import; superseded by JHw, not counted as native closure.'),
      ('joint-agg2-20261028','JHw','Joint actual TX1/TX2 fixture acceptance on one saved vector established under JHe_SHARealization and FixturePdaRuntime, with explicit distinct heaps and same SDK. Model non-vacuity, not arbitrary-adversary native refinement.'),
      ('joint-sha453-20261028','JHx','453 tree SHA equations proved; JHx_Joint.source removes only JHe_SHARealization, retains FixturePdaRuntime and identical joint conclusion. Fixture non-vacuity only, no native syscall/ELF/security theorem.'),
    ]
    result=[]
    for packet,pre,decision in records:
        directory='evidence/'+packet+'/'
        evidence=sorted(p for p in s.tree if p.startswith(directory) and '/' not in p[len(directory):] and
            (p.endswith('.md') or any(x in Path(p).name for x in ['VALIDATION.json','VERIFICATION.json','RESULTS.json','FEATURE_BODY_AUDIT.json','FEATURE_AUDIT.json','PROPERTY_AUDIT.json','STATEMENT_COMPARE.json'])) and s.tree[p][1]<2*1024*1024)
        if pre=='NCN':
            for a in ['NCN_K059','NCN_K060','NCN_K061','NCN_K062']:
                evidence.extend([directory+a+'/receipt.json',directory+a+'/stdout.log',directory+a+'-graph-check.json'])
        assert evidence,(pre,'missing packet')
        for p in evidence:s.read(p)
        result.append(dict(prefix=pre,packet=packet,disposition=decision,evidence=evidence,native_status_promotion=False))
    return result


def summary(d, original):
    rf=d['refresh'];rows=d['rows']
    baseline_by={r['row']:r for r in json.loads((HERE.parent/'native-compledger-20261028'/'NCZ_LEDGER.json').read_text())['rows']}
    changes=[r for r in rows if baseline_by[r['row']]['bridge_status']!=r['bridge_status']]
    lines=['# NDK authoritative native composition ledger','',
      'Pinned research head `'+d['baseline_revision']+'`; frozen Rust `'+d['frozen_revision']+'`. **Deployed 100-bit target not yet established.**','',
      'NCZ reconstruction is refreshed with explicit NDD/NDF/NDG decisions and all merged packet reviews. Local conditional credit retains the exact domain, reference/cohort carrier, dictionary selection and physical interpretation. Every composed row remains OPEN; this audit discharges no security or native caller premise.','',
      '| Inventory | Conditional before | Conditional after | OPEN before | OPEN after | Quarantined before/after |','|---|---:|---:|---:|---:|---:|']
    for tx in ['TX1','TX2','all_rows','unique_functions']:
        a=rf['previous_coverage'][tx]['local_bridge_status'];b=d['coverage'][tx]['local_bridge_status']
        lines.append(f"| {tx} | {a.get('CLOSED-CONDITIONAL',0)} | {b.get('CLOSED-CONDITIONAL',0)} | {a.get('OPEN',0)} | {b.get('OPEN',0)} | {a.get('quarantined',0)}/{b.get('quarantined',0)} |")
    lines += ['',f"Changed inventory rows: **{len(changes)}**. Composed OPEN: **587/587**, unconditional CLOSED: **0**. Trust-only body credit: **0**.",'',
      f"Recomputed minimum reachability-cover frontier: **{rf['previous_frontier_size']} → {len(d['critical_path']['frontier'])} SCC representatives**. This graph statistic need not decrease when leaves close. It is neither a runtime critical path nor a sufficient proof set.",'',
      '## Admitted and rejected frontier deltas','', '| Function | Decision | Domain / remaining obligation |','|---|---|---|']
    for r in rf['decisions']:
        lines.append('| `'+r['function']+'` | '+r['decision']+' | '+(r['domain']+'; '+r['reason']).replace('|','\\|').replace('\n',' ')+' |')
    lines += ['','## Other merged and inherited results','']
    for p in rf['packet_reviews']:
        lines.append('- **'+p['prefix']+'**: '+p['disposition']+' Pinned reports: '+', '.join('`'+x+'`' for x in p['evidence'] if x.endswith(('HANDOFF.md','EVALUATION.md')))+'.')
    lines += ['', 'No NDE_/NDH_/NDI_ artifact exists in this pinned merged tree. Unmerged work is not imported. KNF/KNG replacements were already counted: no double-count and no global quarantine lift. Historical quarantined harnesses remain listed verbatim in `quarantine`; mark and the release observer stay quarantined.','',
      '## Reproduction','',
      '`python3 evidence/native-ledger2-20261028/NDK_validate.py` reconstructs all rows, hashes, claims, evidence, graph and summary without rewriting. `--write` explicitly regenerates. `NDK_tests.py` reruns the inherited NCZ mutations on this snapshot and additional feature/theorem/control/delta/coverage/frontier checks. The original NCZ snapshot and files are retained unchanged; its full current-head CLI correctly refuses corpus drift.','',
      'Every selected new native run requires an exact single-harness positive or one semantic failed control, frozen lock/source checks, all-crate feature list and deployed helper/program selection. Each new theorem must match its successful archived source and exact standard-axiom audit. Python verifies these indexed assertions; manual statement/source association remains an audited trust boundary, not a new semantic prover. No Lean/Kani/Rust/SBF or host job ran here. No wallet/key operation.','',
      '## Current graph and inherited semantics','']
    # Keep the full freshly computed frontier and original interpretation text,
    # replacing the obsolete reproduction instructions and snapshot-specific prose.
    graph=original.split('## Critical path\n',1)[1].split('## Reproduction and boundaries',1)[0]
    lines.append(graph)
    return '\n'.join(lines).rstrip()+'\n'


def finish_refresh(d):
    old=json.loads((HERE.parent/'native-compledger-20261028'/'NCZ_LEDGER.json').read_text())
    before={r['row']:r for r in old['rows']}
    d['refresh']['changed_rows']=[dict(row=r['row'],function=r['function'],before=before[r['row']]['bridge_status'],after=r['bridge_status'],admitted_claims=[c for c in r['selected_claims'] if '::refresh::' in c]) for r in d['rows'] if before[r['row']]['bridge_status']!=r['bridge_status']]
    for c in d['claims']:
        history={q['receipt'] for q in c.get('replaced_quarantined_support',[])}
        c['historical_quarantined_receipts']=sorted(history & set(c['receipts']))
        c['active_support_receipts']=sorted(set(c['receipts'])-history)
    for r in d['rows']:
        r['reviewed_packet_updates']=[dict(prefix=p['prefix'],disposition=p['disposition'],evidence=p['evidence']) for p in d['refresh']['packet_reviews'] if any(m['path'].startswith('evidence/'+p['packet']+'/') for m in r['discovery_mentions'])]
        if r['function']=='crates/aspis-r1-cost-probe/src/verifier.rs::BatchedWeights::value':
            r['pending_native_domain_extension']=dict(prefix='NCN',domain='Every valid64-row Vec and index<64; selected limbs modP via row contract and paired reducer',native_receipts=['NCN_K059','NCN_K060','NCN_K061','NCN_K062'],deployed_credit=False,remaining='Per-crate feature/body association and actual parent/dictionary installation; inherited NCI local domain is retained as selected credit.')
        if r['function']=='crates/aspis-r1-cost-probe/src/verifier.rs::checkpoint':
            r['model_caller_domain_progress']=dict(prefix='NDA',claim='Model-only exact residual domain equivalence on the SAME NCU pre-writer Prefix; no native call identification.',discharged_model_groups=['S2','22 query bounds','query distinctness','weights length64','next10','canonical weights','gamma','kappa','alpha[2]','rho','semanticAlpha[10]','claim'],remaining_model_groups=['coordinates[4]','rhs','power'],retained_leaf_hypotheses=['same-prefix local append correctness','chronological digest calls','oracle interpretation'],native_DriverEstablishedDomain='OPEN',evidence=['evidence/native-drvdom3-20261028/NDA_HANDOFF.md','evidence/native-drvdom2-20261028/NCU_HANDOFF.md','evidence/native-drvdom-20261028/NCT_HANDOFF.md'])


def validate_refresh(d):
    """Extra structural gates; collect() independently reconstructs everything."""
    assert d['baseline_revision']=='898a8b0da7703af67b676b18b575236940830283'
    assert d['refresh']['associations_sha256']==sha((HERE/'NDK_ASSOCIATIONS.json').read_bytes())
    assert d['refresh']['other_merged_frontier_deltas']==[]
    assert d['refresh']['quarantine_lift'] is False
    claims={c['claim_id']:c for c in d['claims']}
    assert len(claims)==len(d['claims'])
    forbidden={q['receipt'] for q in d['quarantine']}
    statuses={}
    for c in claims.values():
        if '::refresh::' in c['claim_id'] and c['admissible_local_credit']:
            assert c['rule14_dependency_audit']
            assert c['theorem_associations'] and c['native_feature_checks']
            for th in c['theorem_associations']:
                assert th['source_sha256']==d['evidence_manifest'][th['source']]['sha256']
                assert th['receipt'] in c['receipts']
            for f in c['native_feature_checks']:
                assert f['all_crates_recorded']>=400
                assert len(f['statement_optimized_features'])==12
        if c['admissible_local_credit']:
            assert set(c['active_support_receipts']) | set(c['historical_quarantined_receipts'])==set(c['receipts'])
            assert not forbidden.intersection(c['active_support_receipts']), 'quarantined receipt dependency'
            assert set(c['historical_quarantined_receipts']) <= {q['receipt'] for q in c['replaced_quarantined_support']}
            if c['historical_quarantined_receipts']:
                assert any('/kani-k2leaf-20261028/' in p for p in c['active_support_receipts']), 'missing static replacement receipts'
    for r in d['rows']:
        cs=[claims[c] for c in r['claim_ids']]
        admissible={c['claim_id'] for c in cs if c['admissible_local_credit']}
        chosen=sorted(admissible,key=lambda cid:(cid.startswith('P6::') is False,cid))[:1]
        assert r['selected_claims']==chosen,('selected claim drift',r['row'])
        expected=('CLOSED-CONDITIONAL' if admissible else 'quarantined' if any(c['quarantined_support'] for c in cs) else 'OPEN')
        assert r['bridge_status']==expected,('local status not supported',r['row'])
        statuses[r['function']]=expected
        assert r['composed_status']=='OPEN','no new execution certificate in this refresh'
        if 'pending_native_domain_extension' in r:
            assert r['pending_native_domain_extension']['deployed_credit'] is False
        for update in r['reviewed_packet_updates']:
            assert all(p in d['evidence_manifest'] for p in update['evidence'])
        if 'model_caller_domain_progress' in r:
            m=r['model_caller_domain_progress']
            assert m['native_DriverEstablishedDomain']=='OPEN'
            assert m['remaining_model_groups']==['coordinates[4]','rhs','power']
            assert all(p in d['evidence_manifest'] for p in m['evidence'])
    for tx in ['TX1','TX2','all_rows']:
        chosen=[r for r in d['rows'] if tx=='all_rows' or r['transaction']==tx]
        c=d['coverage'][tx]
        assert c['rows']==len(chosen)
        assert c['local_bridge_status']==dict(collections.Counter(r['bridge_status'] for r in chosen)), 'coverage mismatch'
        assert c['composed_status']=={'OPEN':len(chosen)}
    assert d['coverage']['unique_functions']['local_bridge_status']==dict(collections.Counter(statuses.values()))
    # Independently verify terminal OPEN SCC coverage and representative counts
    # from the delivered canonical adjacency, avoiding a copied frontier value.
    graph={r['function']:set(r['canonical_callees']) for r in d['rows']}
    def reach(start):
        seen=set();todo=list(graph[start])
        while todo:
            n=todo.pop()
            if n not in seen:seen.add(n);todo.extend(graph[n])
        return seen-{start}
    down={n:reach(n) for n in graph}
    opens={n for n,status in statuses.items() if status in ['OPEN','quarantined']}
    terminal=set()
    for n in opens:
        group={n}|{m for m in down[n] if n in down[m]}
        if not (down[n]&opens)-group:
            terminal.add(tuple(sorted(group)))
    got=set()
    for f in d['critical_path']['frontier']:
        n=f['representative'];group=tuple(f['all_scc_members'])
        assert n in opens and n in group
        assert f['open_scc_members']==sorted(set(group)&opens)
        assert group not in got
        got.add(group)
        up={m for m in graph if n in down[m]}
        assert f['dependent_functions']==len(up)
        assert f['dependent_rows']==sum(r['function'] in up for r in d['rows'])
    assert got==terminal, 'frontier differs from terminal OPEN SCCs'
    assert all(any(f['representative']==n or f['representative'] in down[n] for f in d['critical_path']['frontier']) for n in opens)


def check_delta_association(spec,row):
    pre=spec['id'].split('::')[0]
    actual=[(n['attempt'],n['positive']) for n in spec['native']]
    theorem=spec['theorems'][0]['name']
    if pre=='NDD':
        assert actual==[(row['kani_attempt'],True),(row['negative_control'],False)], 'native delta association mismatch'
        assert theorem==row['lean_theorem']
        assert spec['theorems'][0]['attempt']==row['lean_attempt']
    elif pre=='NDG':
        assert actual==[(a,i==0) for i,a in enumerate(row['kani'])], 'native delta association mismatch'
        assert theorem==row['theorem']
    else:
        assert pre=='NDF'
        expected={
          'opening':([2],[3],'NDF_OpeningBridge.reference'),
          'batch_key_at':([10,11],[12,13],'NDF_ScalarBridge.key'),
          'same_batch_index':([14,15],[16,17],'NDF_ScalarBridge.same_index'),
          'same_batch_leaf':([18,19,22],[20,21,23],'NDF_LeafBridge.same_leaf'),
          "Prefix<'a>::record":([48],[49],'NDF_RecordBridge.reference'),
          "ValidatedRecord<'a>::framed":([38],[39],'NDF_ScalarBridge.framed')}
        pos,neg,t=expected[row['function'].split('.rs::')[1]]
        assert actual==[(f'NDF_K{n:03}',p) for p,ns in [(True,pos),(False,neg)] for n in ns], 'native delta association mismatch'
        assert theorem==t
        assert t in row['reference_and_cohort']
