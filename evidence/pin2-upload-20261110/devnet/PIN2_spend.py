#!/usr/bin/env python3
"""PIN2 devnet re-run: NPC_spend.py with the aspis-upload program, a new verifier and
seeded per-payment accounts that are closed after settlement.

usage: PIN2_spend.py PIN2_devnet.json RECEIPT_DIR

Same fixture flow as NPC_ (mint, registry under the new verifier, fresh Pool state under
the EXISTING Pool program, two deposits, forest checkpoint, transfer then withdrawal with
replay and mutated-proof negatives). Differences, per payment:
  * proof/statement accounts: CreateAccountWithSeed(payer, seed, owner = upload program),
    uploads are aspis-upload WRITEs signed by the payer only (chunk 3,763; 16 + 1);
  * verifier checkpoint: CreateAccountWithSeed(payer, "c0"+tag, 1,768, owner = verifier);
  * after the negatives and the proof restore, ONE close transaction in fixed order
    [proof, statement, checkpoint], then the negative-test checkpoint close;
  * per-payment accounting: payer delta == fees + rent of every account the payment created
    that is still live (expected: exactly the nullifier marker, plus a root page if one was
    created), and lamports recovered by the closes == rent of the closed accounts.
Never deploys. Do not run without the lead's explicit go; this worker did not run it.
"""
import base64, json, pathlib, sys, time
import PIN2_lib as L
from PIN2_seed_accounts import allocate, check_layout, proof_plan_seeded
from r1_devnet_policy import require_key, created_accounts, state_rent
import subprocess, re, os

C = L.init(sys.argv[1], sys.argv[2]); O = L.O; URL = L.URL; P = C['programs']; UP = C['upload_program']
from r1_devnet_rpc import rpc


def key(name, require_existing=False):
    ns = C['key_namespace']; assert re.fullmatch(r'[A-Za-z0-9_-]+', ns), 'invalid key namespace'
    p = pathlib.Path(C['key_dir']) / f'{ns}-{name}.json'
    if require_existing and not p.exists():
        raise RuntimeError('missing retained key; manual recovery required: ' + str(p))
    if not p.exists():
        subprocess.run([str(L.CLI / 'solana-keygen'), 'new', '--no-bip39-passphrase', '--silent', '-o', str(p)], stdout=subprocess.DEVNULL, check=True)
    os.chmod(p, 0o600)
    return str(p), subprocess.check_output([str(L.CLI / 'solana-keygen'), 'pubkey', str(p)], text=True).strip()


def create_keyed(name, address, owner, size, signer):
    """Fixture accounts (mint, token accounts) keep NPC_'s keypair creation."""
    existing = L.account(address)['value']
    if existing is not None:
        assert existing['owner'] == owner and len(base64.b64decode(existing['data'][0])) == size, f'{name}: unexpected existing account'
        return
    rent = rpc(URL, 'getMinimumBalanceForRentExemption', [size])
    data = (0).to_bytes(4, 'little') + rent.to_bytes(8, 'little') + size.to_bytes(8, 'little') + b58(owner)
    return L.send(name, [ix(L.SYSTEM, [[C['payer'], True, True], [address, True, True]], data)], [L.PAYER_KEY, signer])


def b58(s):
    from PIN2_seed_accounts import b58decode
    return b58decode(s)


def ix(program, accounts, data):
    return {'program': program, 'accounts': accounts, 'data': data.hex()}


L.write('retained-payer', require_key(L.PAYER_KEY, L.CLI, C['payer']))
assert rpc(URL, 'getGenesisHash', []) == C['genesis_hash']
if (O / 'complete.json').exists():
    done = json.load(open(O / 'complete.json')); assert done['programs'] == P and done['payer'] == C['payer'] and done['upload_program'] == UP
    print('Recorded run already complete; use a fresh key_namespace and receipt directory for a new run.'); sys.exit(0)
mintkey, mint = key('spend-mint'); sourcekey, source = key('spend-source'); destkey, dest = key('spend-destination'); govkey, gov = key('spend-governance')
plan = lambda action, **kw: L.plan(action, mint=mint, **kw)
create_keyed('mint-create', mint, L.TOKEN, 82, mintkey)
if not (O / 'mint-initialize.json').exists():
    L.send('mint-initialize', [ix(L.TOKEN, [[mint, False, True]], bytes([20, 6]) + b58(C['payer']) + bytes([0]))])
for label, address, path in [('source', source, sourcekey), ('destination', dest, destkey)]:
    create_keyed(label + '-create', address, L.TOKEN, 165, path)
    L.send(label + '-initialize', [ix(L.TOKEN, [[address, False, True], [mint, False, False]], bytes([18]) + b58(gov))])
L.send('mint-supply', [ix(L.TOKEN, [[mint, False, True], [source, False, True], [C['payer'], True, False]], bytes([7]) + (2000).to_bytes(8, 'little'))])
L.write('mint-setup', {'mint': mint, 'source': source, 'destination': dest, 'token_owner': gov, 'mint_authority': C['payer'], 'decimals': 6, 'supply_base_units': 2000})
setupfile = O / 'setup-plan.json'
arts = C['release_artifacts']
if setupfile.exists():
    setup = json.load(open(setupfile))
else:
    setup = plan('setup', funding_payer=C['payer'], governance=gov, activation_slot=rpc(URL, 'getSlot', [{'commitment': 'finalized'}]) + 100,
                 registry_hash=arts['registry']['sha256'], verifier_hash=arts['devnet_verifier']['sha256']); L.write('setup-plan', setup)
L.send('registry-initialize', [setup['registry_initialize']], [L.PAYER_KEY, govkey])
if not (O / 'registry-schedule.json').exists():
    activation = rpc(URL, 'getSlot', [{'commitment': 'confirmed'}]) + 100
    setup = plan('setup', funding_payer=C['payer'], governance=gov, activation_slot=activation,
                 registry_hash=arts['registry']['sha256'], verifier_hash=arts['devnet_verifier']['sha256']); setup['activation_slot'] = activation; L.write('setup-plan', setup)
L.send('registry-schedule', [setup['schedule']], [L.PAYER_KEY, govkey])
while rpc(URL, 'getSlot', [{'commitment': 'finalized'}]) < setup['activation_slot']:
    time.sleep(2)
L.send('registry-activate', [setup['activate']], [L.PAYER_KEY, govkey])
L.send('registry-freeze', [setup['freeze']], [L.PAYER_KEY, govkey])
L.send('pool-initialize', [setup['initialize']])
deposits = []
for n in range(2):
    d = plan('deposit', note=n, source=source, token_owner=gov, genesis=True)
    if L.account(d['page'])['value'] is not None:
        d = plan('deposit', note=n, source=source, token_owner=gov, genesis=False)
    L.write(f'deposit-{n}-plan', d); L.send(f'deposit-{n}', [d['instruction']], [L.PAYER_KEY, govkey]); deposits.append(d)
cp = plan('checkpoint', sequence=0); L.send('forest-checkpoint', [cp['instruction']]); L.write('forest-checkpoint-plan', cp)

pkdir = pathlib.Path(C['proof_key_dir']); ns = C['key_namespace']
payments = {}
for n, label in enumerate(['transfer', 'withdrawal']):
    send = L.send
    # 1. Per-payment seed tag, retained privately before anything is proved or funded.
    seeds = allocate(pkdir / f'{ns}-{label}-pin2-seeds.json', {'label': label, 'payer': C['payer'], 'upload_program': UP, 'verifier': P['verifier'], 'pool': P['pool'], 'mint': mint})
    tag = seeds['pin2_tag']
    lay = check_layout(plan('pin2_layout', pin2_tag=tag), C['payer'], UP, P['verifier'], tag); L.write(label + '-pin2-layout', lay)
    identity = {**P, 'payer': C['payer'], 'mint': mint, 'action': 'prove', 'note': n, 'withdrawal': n == 1, 'destination': dest,
                'checkpoint': cp['checkpoint'], 'public_account': lay['statement']['address'], 'verifier_checkpoint': lay['checkpoint']['address'],
                'upload_program': UP, 'pin2_tag': tag}
    root = pkdir / f'{ns}-{label}-client64-proof-private'
    p, attempt = proof_plan_seeded(root, identity, lay,
        lambda: {'lane_bytes': L.readhex(deposits[n]['output_lane'], P['pool']), 'checkpoint_bytes': L.readhex(cp['checkpoint'], P['pool'])},
        L.invoke, lambda address: L.account(address)['value'] is None, O / (label + '-proof-plan.json'))
    L.write(label + '-proof-plan', p); L.write(label + '-selected-attempt', attempt)
    proof = (root / 'proof' / 'proof.bin').read_bytes(); public = (root / 'proof' / 'statement.bin').read_bytes()
    assert len(proof) == p['proof_bytes'] > L.AFTERSTATE_BYTES
    proof_entry = lay['proof_attempts'][attempt['index']]
    # 2. Accounts and uploads.
    L.create_seeded(label + '-proof-create', proof_entry, len(proof)); L.create_seeded(label + '-public-create', lay['statement'], len(public))
    ps = L.upload(label + '-proof-upload', proof_entry, proof); ss = L.upload(label + '-statement-upload', lay['statement'], public)
    assert (ps['count'], ss['count']) == (p['proof_upload_count'], 1), 'upload count changed'
    L.write(label + '-uploads-phase', {'wall_seconds': ps['wall_seconds'] + ss['wall_seconds'], 'proof_count': ps['count'], 'statement_count': ss['count'], 'compute_units': ps['compute_units'] + ss['compute_units']})
    L.create_seeded(label + '-checkpoint-create', lay['checkpoint'], L.CHECKPOINT_BYTES)
    # 3. TX1 and TX2.
    send(label + '-stage1', [p['stage1']]); send(label + '-stage2', [p['settle']])
    verifiercp = lay['checkpoint']['address']
    readback = {a: L.account(a) for a in [p['marker'], p['output_lane'], setup['vault'], dest, verifiercp]}; L.write(label + '-readback', readback)
    assert readback[p['marker']]['value'] is not None, 'settled nullifier marker missing'
    validation = plan('validate_settlement', note=n, lane_bytes=base64.b64decode(readback[p['output_lane']]['value']['data'][0]).hex(),
                      marker_bytes=base64.b64decode(readback[p['marker']]['value']['data'][0]).hex(), candidate_bytes=proof[:L.AFTERSTATE_BYTES].hex())
    L.write(label + '-settlement-validation', validation)
    vault_amount = int.from_bytes(base64.b64decode(readback[setup['vault']]['value']['data'][0])[64:72], 'little')
    destination_amount = int.from_bytes(base64.b64decode(readback[dest]['value']['data'][0])[64:72], 'little')
    assert (vault_amount, destination_amount) == ((2000, 0) if n == 0 else (1750, 250)), 'settlement SPL balance mismatch'
    L.write(label + '-token-balances', {'vault': vault_amount, 'destination': destination_amount})
    # 4. Negatives (as NPC_): replay, mutated stage 1 on a fresh seeded checkpoint, restore.
    replay = send(label + '-replay', [p['settle']], negative=True)
    assert replay['error'] == {'InstructionError': [0, {'Custom': 0x41532026}]}, 'replay did not reject as NullifierAlreadyConsumed'
    after_replay = {a: L.account(a) for a in readback}
    assert all(readback[a]['value'] == after_replay[a]['value'] for a in readback), 'replay changed protected state'
    L.write(label + '-replay-validation', {'error_name': 'NullifierAlreadyConsumed', 'custom_code': 0x41532026, 'protected_accounts_unchanged': True})
    neg = lay['negative_checkpoint']
    L.create_seeded(label + '-negative-checkpoint-create', neg, L.CHECKPOINT_BYTES)
    off = L.AFTERSTATE_BYTES
    mutate = plan('pin2_writes', seed=proof_entry['seed'], body=bytes([proof[off] ^ 1]).hex(), offset=off)['instructions'][0]
    send(label + '-mutate-proof', [mutate])
    negstage = json.loads(json.dumps(p['stage1'])); negstage['accounts'][2][0] = neg['address']
    negative_before = L.account(neg['address'])['value']
    mutation = send(label + '-mutated-stage1', [negstage], negative=True)
    assert mutation['error'] == {'InstructionError': [0, 'InvalidInstructionData']}, 'mutated proof failed for an unexpected reason'
    assert L.account(neg['address'])['value'] == negative_before, 'mutated proof changed zero checkpoint'
    L.write(label + '-mutation-validation', {'error_name': 'InvalidInstructionData', 'fresh_checkpoint_unchanged': True})
    restore = plan('pin2_writes', seed=proof_entry['seed'], body=proof[off:off + 1].hex(), offset=off)['instructions'][0]
    send(label + '-restore-proof', [restore])
    assert bytes.fromhex(L.readhex(proof_entry['address'], UP)) == proof
    # 5. Close: one fixed transaction [proof, statement, checkpoint], then the test-only negative checkpoint.
    closing = plan('pin2_close', pin2_tag=tag, attempt_index=attempt['index'])
    assert closing['order'] == ['proof', 'statement', 'checkpoint']
    assert [a['address'] for a in closing['accounts']] == [proof_entry['address'], lay['statement']['address'], verifiercp]
    # Rent about to be closed, retained before the first close is signed (so a resumed run keeps it).
    held = O / (label + '-close-before.json')
    if not held.exists():
        live = {a['address']: L.account(a['address'])['value'] for a in closing['accounts'] + [neg]}
        assert all(v and v['lamports'] for v in live.values()), 'an account to close is missing before the close'
        L.write(label + '-close-before', {a: v['lamports'] for a, v in live.items()})
    before = json.loads(held.read_text())
    rent_closed = sum(before[a['address']] for a in closing['accounts']); neg_rent = before[neg['address']]
    send(label + '-close', closing['instructions'])
    negclose = plan('pin2_close_one', kind='checkpoint', owner=P['verifier'], seed=neg['seed'])
    send(label + '-negative-checkpoint-close', [negclose])
    after = {a: L.account(a)['value'] for a in before}
    assert all(v is None or v['lamports'] == 0 for v in after.values()), 'closed account still funded'
    # Accounting from finalized getTransaction meta (fee payer = account 0), which exists
    # for every landed transaction including reconciled ones.
    txs = {f.name[:-len('-transaction.json')]: json.loads(f.read_text()) for f in O.glob(label + '-*-transaction.json')}
    names = sorted(txs, key=lambda k: (txs[k]['slot'], k))
    for t in txs.values():
        k0 = t['transaction']['message']['accountKeys'][0]; assert (k0 if isinstance(k0, str) else k0['pubkey']) == C['payer']
    pdelta = lambda t: t['meta']['postBalances'][0] - t['meta']['preBalances'][0]
    fees = sum(t['meta']['fee'] for t in txs.values())
    delta = sum(pdelta(t) for t in txs.values())
    recovered = sum(pdelta(txs[k]) + txs[k]['meta']['fee'] for k in (label + '-close', label + '-negative-checkpoint-close'))
    assert recovered == rent_closed + neg_rent, 'closes did not return exactly the rent'
    created = set()
    for t in txs.values():
        created.update(created_accounts(t))
    live = {a: L.account(a)['value'] for a in sorted(created)}; live = {a: v for a, v in live.items() if v and v['lamports']}
    expected_live = {p['marker']} | ({p['page']} if p.get('needs_zero_page') else set())
    assert set(live) <= expected_live and p['marker'] in live, f'unexpected live accounts after close: {sorted(set(live) - expected_live)}'
    left = sum(v['lamports'] for v in live.values())
    assert -delta == fees + left, 'payer delta != fees + rent of accounts deliberately left'
    tests = {label + x for x in ('-replay', '-mutate-proof', '-mutated-stage1', '-restore-proof', '-negative-checkpoint-create', '-negative-checkpoint-close')}
    prod = [k for k in names if k not in tests]
    production = {'transactions': len(prod), 'fees_lamports': sum(txs[k]['meta']['fee'] for k in prod),
                  'payer_delta_lamports': sum(pdelta(txs[k]) for k in prod),
                  'note': 'the payment alone (creates, uploads, checkpoint create, TX1, TX2, close), without the negative tests'}
    assert -production['payer_delta_lamports'] == production['fees_lamports'] + left
    payments[label] = {'production_path': production, 'transactions': len(names), 'names': names, 'fees_lamports': fees, 'payer_delta_lamports': delta,
                       'rent_closed_lamports': rent_closed, 'negative_checkpoint_rent_lamports': neg_rent,
                       'recovered_lamports': recovered, 'left_live': {a: {'owner': v['owner'], 'lamports': v['lamports'], 'role': 'nullifier marker' if a == p['marker'] else 'root page'} for a, v in live.items()},
                       'left_lamports': left, 'check_payer_delta_eq_fees_plus_left': True,
                       'closed': [a['address'] for a in closing['accounts']] + [neg['address']]}
    L.write(label + '-close-accounting', payments[label])
created = set()
for receipt in O.glob('*-transaction.json'):
    created.update(created_accounts(json.loads(receipt.read_text())))
ledger = []
for address in sorted(created):
    current = L.account(address)['value']
    if current and current['lamports']:
        row = state_rent(address, current, C['payer'], gov)
        if any(address in x['left_live'] for x in payments.values()):
            row['recovery'] = 'Pool nullifier marker (double-spend record): deliberately permanent'
        ledger.append(row)
L.write('rent-ledger', ledger)
L.write('complete', {'settled': ['transfer', 'withdrawal'], 'closed_per_payment': {k: v['closed'] for k, v in payments.items()},
                     'negative_checks': ['transfer-replay', 'withdrawal-replay', 'transfer-mutated-stage1', 'withdrawal-mutated-stage1'],
                     'mint': mint, 'source': source, 'destination': dest, 'fixture_witnesses_public': True, 'programs': P,
                     'upload_program': UP, 'payer': C['payer'], 'key_namespace': ns, 'payments': payments})
