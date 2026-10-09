#!/usr/bin/env python3
"""Reconcile retained baseline, signed wire, independent B model and rollbacks."""
import hashlib,json,pathlib,re,struct,sys
import model
HERE=pathlib.Path(__file__).resolve().parent
historical=json.loads((HERE.parent/'v8-no-work-100-20260907/terminal-query-results.json').read_text())
rows=[];rollbacks=0;cases=0;hashes=set();all_cu=[];all_bytes=[];all_rollbacks=0;after_b_rollbacks=0
for p in sorted((HERE/'evidence/final').glob('*.json')):
    x=json.loads(p.read_text()); r=x['reference']; dec=lambda name:bytes.fromhex(r[name])
    ordinary=p.name.startswith('ordinary'); mode='ordinary' if ordinary else 'maximum'
    shape=f"transfer-{x['source_pairs']}"; seed=int(p.stem.split('-')[-1]); prev=historical[mode]['shapes'][shape][seed-1]
    assert x['proof_sha256']==prev['proof_sha256'] and x['baseline']['cu']==prev['cu']
    assert x['local_txv1_feature_activation']==['txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL',0]
    asq=dec('asq8');assert len(asq)==320
    n=x['destination_prior_receipts']
    prior=[model.h(model.DOMAIN,b'/fixture',model.u64(i)) for i in range(n)]
    assert model.tree_root(prior)==dec('b_old_root')
    s=model.VerifiedSource(dec('source_program'),dec('verifier'),dec('source_master'),dec('source_lane'),dec('proof_account'),
        r['a_old_sequence'],dec('a_old_root'),dec('a_new_root'),asq,asq[216:248],int.from_bytes(asq[248:252],'little'))
    leaf=model.receipt(s,dec('b_program'),dec('b_account'),n,dec('b_old_root'))
    assert leaf==dec('receipt') and model.tree_root(prior+[leaf])==dec('b_new_root')
    state=model.State(s.old_root,s.old_sequence,s.master,s.asset,dec('b_program'),dec('b_account'),prior)
    new=model.transition(state,s,dec('b_old_root'),n,dec('b_new_root'),leaf,model.append_path(prior))
    assert new.a_root==dec('a_new_root') and new.a_sequence==r['a_new_sequence']
    happy=x['cases'][0];assert happy['accepted'] and happy['real_verifier_success']
    hashes.add(x['inbox_elf_sha256'])
    for case in [x['baseline'],x['initialize_B']]+x['cases']:
        wire=bytes.fromhex(case['signed_transaction_hex']);assert len(wire)==case['signed_transaction_bytes']
        assert hashlib.sha256(wire).hexdigest()==case['signed_transaction_sha256']
        assert wire[0]==0x81 and int.from_bytes(wire[4:8],'little')==31
        count=wire[41];pos=42+32*count
        assert struct.unpack('<QIII',wire[pos:pos+20])==(10000,1200000,8388608,262144)
        assert count<=64 and wire[40]<=64 and len(wire)<=4096 and case['cu']<=1200000
        if not case['accepted']:
            assert case['all_protected_unchanged'] and case['protected_before_sha256']==case['protected_after_sha256']
            # These failures have only ordinary transaction fees; account rent
            # and every provisional state write reverted.
            assert case['payer_lamport_decrease']==15000
    all_rollbacks+=sum(not c['accepted'] and c['source_provisionally_settled'] and c['real_verifier_success'] for c in x['cases'])
    after_b_rollbacks+=sum(not c['accepted'] and any('Program data: YXRvbWljOnJlY2VpcHQtdjE=' in s for s in c['logs']) for c in x['cases'])
    all_cu.extend(c['cu'] for c in x['cases']); all_bytes.extend(c['signed_transaction_bytes'] for c in x['cases'])
    by_name={case['name']:case for case in x['cases']}
    for name in ['b-new-root','handoff','later-instruction-failure']:
        c=by_name[name];assert c['real_verifier_success'] and c['source_provisionally_settled'] and not c['accepted'];rollbacks+=1
    assert by_name['exact-replay-fresh-blockhash']['signed_transaction_sha256']!=happy['signed_transaction_sha256']
    source_log="Program 7Q2nGsPg8rbjdxKHK4jxTgEWLTyd9o1X4KMSjCieRmue consumed "
    cryptographic_cu=next(int(s.split(' consumed ')[1].split()[0]) for s in happy['logs'] if s.startswith(source_log))
    rows.append({'case':p.stem,'ordinary':ordinary,'source_pairs':x['source_pairs'],'destination_prior_receipts':n,
        'proof_bytes':x['proof_bytes'],'proof_sha256':x['proof_sha256'],'baseline_cu':x['baseline']['cu'],'atomic_cu':happy['cu'],
        'incremental_cu':happy['cu']-x['baseline']['cu'],'baseline_signed_bytes':x['baseline']['signed_transaction_bytes'],
        'atomic_signed_bytes':happy['signed_transaction_bytes'],'instruction_count':happy['instruction_count'],'addresses':happy['address_count'],
        'verifier_only_cu':cryptographic_cu,'cases':len(x['cases']),'log':str(p.relative_to(HERE))})
    cases+=len(x['cases'])
assert len(rows)==9 and len(hashes)==1
perf=[]
for line in (HERE/'evidence/prover-v1.log').read_text().splitlines():
    if line.startswith('PERF '): perf.append(json.loads(line[5:]))
assert all(p.get('stress_nonce_attempts',0)==0 for p in perf)
prover_seconds=[p['seconds'] for p in perf if p.get('phase')=='prover_total_excludes_setup']
setup=next(p['seconds'] for p in perf if p.get('phase')=='setup_compiler_encoder_matrix')
result={'schema':'aspis.v8.atomic-two-root.measurements.v1','base':'4aaa61e679189b2cf76bfc25c2e3ff8d5c76341e','milestone':'I',
    'relation_changes':False,'proof_byte_increase':0,'message_only':True,'separate_program_owners':True,'production_edits':False,
    'measurements':rows,'maximum_atomic_cu':max(r['atomic_cu'] for r in rows),'maximum_incremental_cu':max(r['incremental_cu'] for r in rows),
    'maximum_signed_transaction_bytes':max(r['atomic_signed_bytes'] for r in rows),'maximum_tested_transaction_cu':max(all_cu),'maximum_tested_transaction_bytes':max(all_bytes),'minimum_tested_headroom_cu':1200000-max(all_cu),'cu_gate':1200000,'approved_single_root_body_cap':40282,
    'remaining_observed_cu_headroom':1200000-max(r['atomic_cu'] for r in rows),'tested_cases':cases,'baseline_cases':len(rows),
    'independent_model_agreements':len(rows),'checked_named_post_source_rollback_cases':rollbacks,'all_post_source_rollback_cases':all_rollbacks,'after_destination_update_rollback_cases':after_b_rollbacks,
    'inbox_elf_sha256':next(iter(hashes)),'inbox_account_bytes':116,'proof_header_bytes':40,'afterstate_bytes':688,
    'maximum_proof_account_bytes':40+688+40282,'inbox_init_transactions_per_fixture':1,'source_transitions_during_setup':0,
    'executed_proof_upload_transactions':0,'executed_proof_seal_transactions':0,'executed_proof_cleanup_transactions':0,
    'proof_lifecycle':'Synthetic sealed account injection; network upload/seal/cleanup costs unmeasured. The retained research ELF exposes ASQ8 only.',
    'host_prover':{'configuration':'pinned-source optimized structured host, overflow checks enabled; not retained fastest arithmetic configuration',
        'setup_seconds':setup,'proving_seconds':prover_seconds,'peak_rss_kib':202780,'wall_seconds':15.02,'swaps':0,'nonce_search_attempts':0},
    'two_full_verifiers_component_sum_estimate_cu':2*max(r['verifier_only_cu'] for r in rows),
    'joint_relation_cu':None,'joint_relation_proof_bytes':None,'global_security_bits':None,'universal_cu_bound':None}
out=HERE/'measurements.json'
if '--check' in sys.argv: assert json.loads(out.read_text())==result
else: out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['tested_cases','independent_model_agreements','maximum_atomic_cu','maximum_incremental_cu','maximum_signed_transaction_bytes','remaining_observed_cu_headroom']}))
