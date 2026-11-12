#!/usr/bin/env python3
"""Aspis one-transaction verifier, freeze run: the spend path, end to end.

usage: ASPIS_spend.py config.json RECEIPT_DIR

This is FV_spend.py of evidence/future-version-20261111/devnet with ONE addition: before the withdrawal settles,
three redirect attempts (step 3b), each of which must fail and change nothing. Everything below is that script's text.

PIN2_spend.py adapted. Same fixture flow (mint, registry under the new verifier, fresh Pool
state under the EXISTING Pool program, two deposits, forest checkpoint, transfer then
withdrawal). Differences, per payment:
  * the prover's proof is re-packed into the summed format by the planner ("one_tx": true)
    and checked there with the verifier's own function; proof account 56,503 bytes;
  * no statement account, no stage 1: verification and settlement are ONE transaction;
  * open: ONE transaction [create proof account, create checkpoint account, write the
    58-byte tail], then 15 full 3,763-byte writes (the frozen chunk), signed against one
    blockhash and sent together (config "uploads_together", default true);
  * the unchanged Pool still passes a verifier-owned 1,768-byte checkpoint account to the
    verifier, which does not read it; it is created zeroed and closed afterwards;
  * negatives BEFORE the settlement: one byte changed in the certificate, then one byte in a
    Merkle node; each settlement attempt must fail and change no protected account; the
    byte is restored after each. After the settlement: a replay must fail;
  * close: ONE transaction [upload CLOSE proof, verifier close checkpoint, transfer of
    everything the session key holds back to the payer];
  * ONE approval: the payer (standing for the user's wallet) signs exactly one transaction
    per payment, the open, which also funds a fresh session key. The session key is the base
    of the seed-derived accounts and signs every other transaction of the payment; the close
    empties it. Nothing but the nullifier marker rent and the fees stays spent.
Production path per payment: 1 + 15 + 1 + 1 = 18 transactions, one of them signed by the payer.

Config "mode": "evidence" (default) is the flow above: every transaction awaited to finality and
recorded, with the negative tests. "mode": "timing" pays the way a wallet would and measures it:
all 18 transactions of a payment are signed first (one blockhash), then sent in four phases
(open; the 15 writes together; settlement; close), each phase awaited to confirmation only. The
clock runs from the first send. No negative tests in that mode; the same validation and accounting
run afterwards on the finalized transactions.
Never deploys. Run against devnet only with the owner's go.
"""
import base64, json, os, pathlib, re, subprocess, sys, time
import PIN2_lib as L
from PIN2_seed_accounts import allocate, check_layout, proof_plan_seeded, b58decode as b58
from r1_devnet_policy import require_key, created_accounts, state_rent

C = L.init(sys.argv[1], sys.argv[2]); O = L.O; URL = L.URL; P = C['programs']; UP = C['upload_program']
from r1_devnet_rpc import rpc as _rpc_once
import NPC_record


def rpc(url, method, params):
    """The shared transport, plus a bounded retry of the public endpoint's transient history error (-32019,
    "Failed to query long-term storage; please try again"), which otherwise stops the run after a transaction has landed."""
    for attempt in range(6):
        try:
            return _rpc_once(url, method, params)
        except RuntimeError as e:
            if '-32019' not in str(e) or attempt == 5:
                raise
            time.sleep(3 * (attempt + 1))


L.rpc = NPC_record.rpc = rpc
CU_LIMIT = 1_400_000
MODE = C.get('mode', 'evidence'); assert MODE in ('evidence', 'timing')
EXPECTED = C.get('expected_negative_errors')     # pinned from the rehearsal for a network run


def key(name):
    ns = C['key_namespace']; assert re.fullmatch(r'[A-Za-z0-9_-]+', ns), 'invalid key namespace'
    p = pathlib.Path(C['key_dir']) / f'{ns}-{name}.json'
    if not p.exists():
        subprocess.run([str(L.CLI / 'solana-keygen'), 'new', '--no-bip39-passphrase', '--silent', '-o', str(p)], stdout=subprocess.DEVNULL, check=True)
    os.chmod(p, 0o600)
    return str(p), subprocess.check_output([str(L.CLI / 'solana-keygen'), 'pubkey', str(p)], text=True).strip()


def ix(program, accounts, data):
    return {'program': program, 'accounts': accounts, 'data': data.hex()}


def create_keyed(name, address, owner, size, signer):
    existing = L.account(address)['value']
    if existing is not None:
        assert existing['owner'] == owner and len(base64.b64decode(existing['data'][0])) == size, f'{name}: unexpected existing account'
        return
    rent = rpc(URL, 'getMinimumBalanceForRentExemption', [size])
    data = (0).to_bytes(4, 'little') + rent.to_bytes(8, 'little') + size.to_bytes(8, 'little') + b58(owner)
    return L.send(name, [ix(L.SYSTEM, [[C['payer'], True, True], [address, True, True]], data)], [L.PAYER_KEY, signer])


def send_together(label, names, instructions, keys, sender):
    """Send independent single-instruction transactions at once and wait once.

    All are signed against one blockhash and sent without waiting for one another; the time
    until every one is confirmed is recorded. Each signed transaction is retained as an attempt
    record before it is sent, so L.send then reconciles it by name (waits for finality, fetches
    the metadata) and, if one never landed, sends that one again by itself. Used for the proof
    writes only: they touch distinct byte ranges of one account, so their order does not matter,
    and the whole account is read back afterwards.
    """
    todo = [(n, i) for n, i in zip(names, instructions) if not (O / (n + '.json')).exists() and not list(O.glob(n + '-attempt-*.json'))]
    timing = None
    if todo:
        bh = rpc(URL, 'getLatestBlockhash', [{'commitment': 'confirmed'}])['value']
        signed = [(n, L.invoke({'keys': keys, 'instructions': [i], 'blockhash': bh['blockhash']})) for n, i in todo]
        started = time.time()
        for n, t in signed:
            L.write(f'{n}-attempt-0', {'signature': t['signature'], 'blockhash': bh, 'simulation_error': None, 'serialized_bytes': t['bytes'],
                                       'started_unix': started, 'sent_together': True})
        t0 = time.monotonic(); errors = {}
        for n, t in signed:
            try:
                rpc(URL, 'sendTransaction', [base64.b64encode(bytes.fromhex(t['hex'])).decode(), {'encoding': 'base64', 'skipPreflight': True, 'maxRetries': 5}])
            except Exception as e:
                errors[n] = str(e)
        sent = time.monotonic() - t0
        sigs = [t['signature'] for _, t in signed]; confirmed = None; slots = []
        while time.monotonic() - t0 < 90:
            st = rpc(URL, 'getSignatureStatuses', [sigs])['value']
            if all(x and x['confirmationStatus'] in ('confirmed', 'finalized') for x in st):
                confirmed = time.monotonic() - t0; slots = [x['slot'] for x in st]; break
            time.sleep(0.4)
        timing = {'count': len(signed), 'send_wall_seconds': sent, 'all_confirmed_wall_seconds': confirmed, 'send_errors': errors,
                  'slots': sorted(set(slots)), 'note': 'wall time from the first send until every write is confirmed; None if not all confirmed within 90 s'}
        L.write(label + '-sent-together', timing)
    results = [sender(n, [i]) for n, i in zip(names, instructions)]
    return results, timing


SEND_URLS = C.get('send_urls') or [URL]      # a payment's transactions are broadcast to every endpoint listed


def post(url, method, params):
    """One JSON-RPC call, no pacing, no retry. Errors never carry the endpoint URL (it may hold an API key)."""
    import urllib.request, urllib.error
    req = urllib.request.Request(url, json.dumps({'jsonrpc': '2.0', 'id': 1, 'method': method, 'params': params}).encode(), {'Content-Type': 'application/json'})
    try:
        with urllib.request.urlopen(req, timeout=30) as r:
            v = json.load(r)
    except urllib.error.HTTPError as e:
        raise RuntimeError(f'HTTP {e.code}') from None
    except OSError as e:
        raise RuntimeError(type(e).__name__) from None
    if 'error' in v:
        raise RuntimeError(v['error'])
    return v['result']


def rpc_now(method, params):
    """A status read without the shared pacing, retried briefly."""
    for attempt in range(6):
        try:
            return post(URL, method, params)
        except RuntimeError:
            if attempt == 5:
                raise
            time.sleep(0.4 * (attempt + 1))


def broadcast(signed_hex):
    """Send one signed transaction to every endpoint; it is enough that one accepts it (the signature can land once)."""
    wire = base64.b64encode(bytes.fromhex(signed_hex)).decode(); accepted = 0; refused = []
    for u in SEND_URLS:
        try:
            post(u, 'sendTransaction', [wire, {'encoding': 'base64', 'skipPreflight': True, 'maxRetries': 5}]); accepted += 1
        except RuntimeError as e:
            refused.append(str(e)[:120])
    if not accepted:
        raise RuntimeError(f'no endpoint accepted the transaction: {refused}')
    return accepted


def wallet_payment(label, phases):
    """Sign everything, then send phase by phase, waiting for confirmation only. phases: [(phase, [(name, instructions, keys)])].

    Each signed transaction is retained as an attempt record before anything is sent, so the evidence
    path that follows reconciles it by name at finality instead of sending it again.
    """
    bh = rpc(URL, 'getLatestBlockhash', [{'commitment': 'confirmed'}])['value']
    t_sign = time.monotonic(); signed = {}
    for _, txs in phases:
        for name, ixs, keys in txs:
            signed[name] = L.invoke({'keys': keys, 'instructions': ixs, 'blockhash': bh['blockhash']})
    sign_seconds = time.monotonic() - t_sign; started = time.time()
    for name, t in signed.items():
        L.write(f'{name}-attempt-0', {'signature': t['signature'], 'blockhash': bh, 'simulation_error': None, 'serialized_bytes': t['bytes'],
                                      'started_unix': started, 'wallet_mode': True})
    t0 = time.monotonic(); rows = []
    for phase, txs in phases:
        begin = time.monotonic() - t0; sigs = [signed[name]['signature'] for name, _, _ in txs]
        from concurrent.futures import ThreadPoolExecutor
        with ThreadPoolExecutor(max_workers=16) as workers:      # a phase's transactions leave concurrently
            accepted = list(workers.map(broadcast, [signed[name]['hex'] for name, _, _ in txs]))
        sent = time.monotonic() - t0
        while True:
            st = rpc_now('getSignatureStatuses', [sigs])['value']
            bad = [x['err'] for x in st if x and x['err']]
            if bad:
                raise RuntimeError(f'{label} {phase}: transaction failed: {bad}')
            if all(x and x['confirmationStatus'] in ('confirmed', 'finalized') for x in st):
                break
            if time.monotonic() - t0 > 75:
                raise RuntimeError(f'{label} {phase}: not confirmed in 75 s')
            time.sleep(0.35)
        rows.append({'phase': phase, 'transactions': len(txs), 'endpoints_accepting': sorted(set(accepted)), 'begin_seconds': begin, 'sent_seconds': sent,
                     'confirmed_seconds': time.monotonic() - t0, 'slots': sorted({x['slot'] for x in st})})
    by = {r['phase']: r for r in rows}
    out = {'clock': 'wall seconds from the first send, all transactions signed beforehand; confirmation, not finality',
           'send_endpoints': len(SEND_URLS),
           'signing_seconds_in_this_harness': sign_seconds, 'phases': rows,
           'first_send_to_settled_seconds': by['settle']['confirmed_seconds'], 'first_send_to_closed_seconds': by['close']['confirmed_seconds'],
           'slots_from_open_to_settle': by['settle']['slots'][-1] - by['open']['slots'][0]}
    L.write(label + '-wallet-timing', out)
    print(label, 'wallet-timing', json.dumps(out), flush=True)
    return out


L.write('retained-payer', require_key(L.PAYER_KEY, L.CLI, C['payer']))
assert rpc(URL, 'getGenesisHash', []) == C['genesis_hash']
if (O / 'complete.json').exists():
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
payments = {}; observed_errors = {}
FEE1, FEE2 = 15000, 20000     # one and two signatures at the client's fixed priority fee; asserted on every landed transaction
MARKER_BYTES = 208
balance = lambda a: rpc(URL, 'getBalance', [a, {'commitment': 'finalized'}])['value']
transfer = lambda src, dst, lamports: ix(L.SYSTEM, [[src, True, True], [dst, False, True]], (2).to_bytes(4, 'little') + lamports.to_bytes(8, 'little'))
for n, label in enumerate(['transfer', 'withdrawal']):
    # 0. The session key: retained (0600) before anything is proved or funded. It is the base of the
    # payment's seed-derived accounts, the fee payer of every transaction after the open, and is emptied by the close.
    sessionkey, session = key(f'{label}-session')
    splan = lambda action, **kw: plan(action, **{**kw, 'payer': session})

    def send(name, ixs, negative=False):
        saved = L.C; L.C = {**saved, 'payer': session}     # the recorder snapshots the fee payer it is told
        try:
            return L.send(name, ixs, [sessionkey], negative=negative)
        finally:
            L.C = saved
    # 1. Per-payment seed tag, retained privately before anything is proved or funded.
    seeds = allocate(pkdir / f'{ns}-{label}-pin2-seeds.json', {'label': label, 'payer': session, 'upload_program': UP, 'verifier': P['verifier'], 'pool': P['pool'], 'mint': mint})
    tag = seeds['pin2_tag']
    lay = check_layout(splan('pin2_layout', pin2_tag=tag), session, UP, P['verifier'], tag); L.write(label + '-pin2-layout', lay)
    # 'public_account' is the seed-derived statement address. It is never created on this route;
    # it is named only because the retained-mapping check compares the (unsent) stage 1 roles.
    identity = {**P, 'payer': session, 'mint': mint, 'action': 'prove', 'note': n, 'withdrawal': n == 1, 'destination': dest,
                'checkpoint': cp['checkpoint'], 'public_account': lay['statement']['address'], 'verifier_checkpoint': lay['checkpoint']['address'],
                'upload_program': UP, 'pin2_tag': tag, 'one_tx': True}
    root = pkdir / f'{ns}-{label}-client64-proof-private'
    p, attempt = proof_plan_seeded(root, identity, lay,
        lambda: {'lane_bytes': L.readhex(deposits[n]['output_lane'], P['pool']), 'checkpoint_bytes': L.readhex(cp['checkpoint'], P['pool'])},
        L.invoke, lambda address: L.account(address)['value'] is None, O / (label + '-proof-plan.json'))
    L.write(label + '-proof-plan', p); L.write(label + '-selected-attempt', attempt)
    assert p['one_tx'] is True, 'planner did not take the one-transaction route'
    proof = (root / 'proof' / 'proof.bin').read_bytes()
    assert len(proof) == p['proof_bytes'] == L.AFTERSTATE_BYTES + 55815, 'summed proof length'
    assert proof[L.AFTERSTATE_BYTES:L.AFTERSTATE_BYTES + 8] == b'ASPIS\x00\x00\x02', 'Aspis one-transaction proof format magic'
    proof_entry = lay['proof_attempts'][attempt['index']]; cpe = lay['checkpoint']; verifiercp = cpe['address']
    # 2. Open: both accounts and the tail in one transaction, then the 15 full chunks.
    full = (len(proof) // L.CHUNK) * L.CHUNK
    assert (full, len(proof) - full) == (15 * L.CHUNK, 58)
    rent_proof, rent_cp, rent_marker = (rpc(URL, 'getMinimumBalanceForRentExemption', [size]) for size in (len(proof), L.CHECKPOINT_BYTES, MARKER_BYTES))
    assert not p.get('needs_zero_page'), 'this fixture never creates a root page in the settlement; the funding below does not cover one'
    mk_proof = splan('pin2_create', owner=proof_entry['owner'], seed=proof_entry['seed'], lamports=rent_proof, space=len(proof))
    mk_cp = splan('pin2_create', owner=cpe['owner'], seed=cpe['seed'], lamports=rent_cp, space=L.CHECKPOINT_BYTES)
    assert (mk_proof['address'], mk_cp['address']) == (proof_entry['address'], verifiercp), 'planner create address differs'
    tail = splan('pin2_writes', seed=proof_entry['seed'], body=proof[full:].hex(), offset=full)
    assert tail['address'] == proof_entry['address'] and tail['count'] == 1
    # The one transaction the payer signs. It funds the session key with: the two refundable rents, the marker
    # rent the settlement spends, the fees of the session key's transactions (15 writes, settlement, close; plus
    # this run's seven test transactions), and a margin that keeps the key rent-exempt in between. All but the
    # marker rent and the fees returns in the close.
    session_transactions = 15 + 1 + 1 + ((7 + (3 if n == 1 else 0)) if MODE == 'evidence' else 0); margin = 3_000_000   # +3: the withdrawal's redirect attempts (step 3b)
    fund = rent_proof + rent_cp + rent_marker + session_transactions * FEE1 + margin
    open_ixs = [transfer(C['payer'], session, fund), mk_proof['instruction'], mk_cp['instruction'], tail['instructions'][0]]
    w = splan('pin2_writes', seed=proof_entry['seed'], body=proof[:full].hex())
    assert w['address'] == proof_entry['address'] and w['chunk'] == L.CHUNK and w['count'] == 15
    close_ixs = lambda sweep: [splan('pin2_close_one', kind='upload', owner=UP, seed=proof_entry['seed']),
                               splan('pin2_close_one', kind='checkpoint', owner=P['verifier'], seed=cpe['seed']),
                               transfer(session, C['payer'], sweep)]
    if MODE == 'timing' and not (O / (label + '-wallet-timing.json')).exists() and not (O / (label + '-open.json')).exists() and not list(O.glob(label + '-open-attempt-*.json')):
        assert L.account(session)['value'] is None, 'session key already has an account'
        L.write(label + '-payer-before', {'payer_lamports': balance(C['payer']), 'fund_lamports': fund})
        # Known in advance: the session key pays the two rents, 15 writes and the settlement (which also spends the marker rent).
        session_before_close = fund - rent_proof - rent_cp - rent_marker - 16 * FEE1
        L.write(label + '-close-before', {'accounts': {proof_entry['address']: rent_proof, verifiercp: rent_cp}, 'session_lamports': session_before_close, 'computed_in_advance': True})
        wallet_payment(label, [('open', [(label + '-open', open_ixs, [L.PAYER_KEY, sessionkey])]),
                               ('writes', [(f'{label}-proof-upload-{i}', [one], [sessionkey]) for i, one in enumerate(w['instructions'])]),
                               ('settle', [(label + '-settle', [p['settle']], [sessionkey])]),
                               ('close', [(label + '-close', close_ixs(session_before_close + rent_proof + rent_cp - FEE1), [sessionkey])])])
    started = O / (label + '-payer-before.json')
    if not started.exists():
        assert L.account(session)['value'] is None, 'session key already has an account'
        L.write(label + '-payer-before', {'payer_lamports': balance(C['payer']), 'fund_lamports': fund})
    payer_before = json.loads(started.read_text())['payer_lamports']
    L.send(label + '-open', open_ixs, [L.PAYER_KEY, sessionkey])
    if C.get('uploads_together', True):
        ups, together = send_together(label + '-proof-upload', [f'{label}-proof-upload-{i}' for i in range(15)], w['instructions'], [sessionkey], send)
    else:
        ups, together = [send(f'{label}-proof-upload-{i}', [one]) for i, one in enumerate(w['instructions'])], None
    if MODE == 'evidence':
        assert bytes.fromhex(L.readhex(proof_entry['address'], UP)) == proof, 'upload readback differs'
        cpv = L.account(verifiercp)['value']
        assert cpv['owner'] == P['verifier'] and not any(base64.b64decode(cpv['data'][0])), 'checkpoint account is not a zeroed verifier-owned account'
    L.write(label + '-uploads-phase', {'proof_count': len(ups), 'tail_bytes_in_open': len(proof) - full, 'compute_units': sum(s['compute_units'] for s in ups),
                                       'sent_together': together, 'slots': sorted({s['slot'] for s in ups})})
    # 3. Negatives before the settlement: a changed byte must make the ONE transaction fail and leave state alone.
    protected = [p['marker'], p['output_lane'], p['page'], setup['vault'], dest, setup['master'], verifiercp]
    before = {a: L.account(a)['value'] for a in protected} if MODE == 'evidence' else {}
    assert MODE == 'timing' or before[p['marker']] is None, 'nullifier marker exists before the settlement'
    for name, at in [('cert', L.AFTERSTATE_BYTES + p['off_certificate']), ('node', L.AFTERSTATE_BYTES + p['off_nodes'])] if MODE == 'evidence' else []:
        change = splan('pin2_writes', seed=proof_entry['seed'], body=bytes([proof[at] ^ 1]).hex(), offset=at)['instructions'][0]
        send(f'{label}-{name}-mutate', [change])
        bad = send(f'{label}-{name}-settle', [p['settle']], negative=True)
        assert bad['error'] is not None and {a: L.account(a)['value'] for a in protected} == before, f'{name}: changed proof was accepted or changed state'
        observed_errors.setdefault(name, bad['error'])
        if EXPECTED is not None:
            assert bad['error'] == EXPECTED[name], f'{name}: rejected for an unexpected reason: {bad["error"]}'
        assert bad['error'] == observed_errors[name], f'{name}: the two payments were rejected for different reasons'
        undo = splan('pin2_writes', seed=proof_entry['seed'], body=proof[at:at + 1].hex(), offset=at)['instructions'][0]
        send(f'{label}-{name}-restore', [undo])
        L.write(f'{label}-{name}-validation', {'offset_in_account': at, 'error': bad['error'], 'compute_units': bad['compute_units'], 'protected_accounts_unchanged': True})
    # 3b. Withdrawal only: redirect attempts. The destination is replaced by another token account of the same mint
    # and owner (the fixture source account): in the request and the account list, in the account list only, in the
    # request only. Each must fail and change no protected account and neither token account.
    if MODE == 'evidence' and n == 1:
        db, ob = b58(dest), b58(source); request = bytes.fromhex(p['settle']['data'])
        assert request.count(db) == 1 and sum(a[0] == dest for a in p['settle']['accounts']) == 1, 'destination must occur once in the request and once in the accounts'
        watched = protected + [source]; held0 = {a: L.account(a)['value'] for a in watched}; redirects = {}
        for name, in_request, in_accounts in [('redirect-both', True, True), ('redirect-account', False, True), ('redirect-request', True, False)]:
            moved = dict(p['settle'])
            if in_request:
                moved['data'] = request.replace(db, ob).hex()
            if in_accounts:
                moved['accounts'] = [[source if a[0] == dest else a[0]] + list(a[1:]) for a in p['settle']['accounts']]
            bad = send(f'{label}-{name}-settle', [moved], negative=True)
            assert bad['error'] is not None and {a: L.account(a)['value'] for a in watched} == held0, f'{name}: a redirected withdrawal was accepted or changed state'
            if (C.get('expected_redirect_errors') or {}).get(name) is not None:
                assert bad['error'] == C['expected_redirect_errors'][name], f'{name}: rejected for an unexpected reason: {bad["error"]}'
            redirects[name] = {'error': bad['error'], 'compute_units': bad['compute_units']}
        L.write(f'{label}-redirect-validation', {'destination': dest, 'other_token_account': source, 'attempts': redirects, 'protected_accounts_unchanged': True})
    assert MODE == 'timing' or bytes.fromhex(L.readhex(proof_entry['address'], UP)) == proof, 'proof not restored'
    # 4. THE transaction: verification and settlement.
    settled = send(label + '-settle', [p['settle']])
    assert settled['compute_units'] < CU_LIMIT
    readback = {a: L.account(a) for a in [p['marker'], p['output_lane'], setup['vault'], dest, verifiercp]}; L.write(label + '-readback', readback)
    assert readback[p['marker']]['value'] is not None, 'settled nullifier marker missing'
    assert MODE == 'timing' or readback[verifiercp]['value'] == before[verifiercp], 'the unread checkpoint account changed'
    validation = plan('validate_settlement', note=n, lane_bytes=base64.b64decode(readback[p['output_lane']]['value']['data'][0]).hex(),
                      marker_bytes=base64.b64decode(readback[p['marker']]['value']['data'][0]).hex(), candidate_bytes=proof[:L.AFTERSTATE_BYTES].hex())
    L.write(label + '-settlement-validation', validation)
    vault_amount = int.from_bytes(base64.b64decode(readback[setup['vault']]['value']['data'][0])[64:72], 'little')
    destination_amount = int.from_bytes(base64.b64decode(readback[dest]['value']['data'][0])[64:72], 'little')
    assert (vault_amount, destination_amount) == ((2000, 0) if n == 0 else (1750, 250)), 'settlement SPL balance mismatch'
    L.write(label + '-token-balances', {'vault': vault_amount, 'destination': destination_amount})
    # 5. Replay.
    if MODE == 'evidence':
        replay = send(label + '-replay', [p['settle']], negative=True)
        assert replay['error'] == {'InstructionError': [0, {'Custom': 0x41532026}]}, 'replay did not reject as NullifierAlreadyConsumed'
        assert all(readback[a]['value'] == L.account(a)['value'] for a in readback), 'replay changed protected state'
        L.write(label + '-replay-validation', {'error_name': 'NullifierAlreadyConsumed', 'custom_code': 0x41532026, 'protected_accounts_unchanged': True})
    # 6. Close and sweep: one transaction, fixed order [proof, checkpoint, everything back to the payer].
    closing = [proof_entry['address'], verifiercp]
    held = O / (label + '-close-before.json')
    if not held.exists():
        live = {a: L.account(a)['value'] for a in closing}
        assert all(v and v['lamports'] for v in live.values()), 'an account to close is missing before the close'
        L.write(label + '-close-before', {'accounts': {a: v['lamports'] for a, v in live.items()}, 'session_lamports': balance(session)})
    held_state = json.loads(held.read_text()); rent_closed = sum(held_state['accounts'].values())
    assert rent_closed == rent_proof + rent_cp
    sweep = held_state['session_lamports'] + rent_closed - FEE1
    send(label + '-close', close_ixs(sweep))
    after = {a: L.account(a)['value'] for a in closing + [session]}
    assert all(v is None or v['lamports'] == 0 for v in after.values()), 'closed account or session key still funded'
    payer_after = balance(C['payer'])
    # 7. Accounting. The payer signs nothing else during the payment, so its balance change is the payment's whole cost.
    txs = {f.name[:-len('-transaction.json')]: json.loads(f.read_text()) for f in O.glob(label + '-*-transaction.json')}
    names = sorted(txs, key=lambda k: (txs[k]['slot'], k))
    keys_of = lambda t: [k if isinstance(k, str) else k['pubkey'] for k in t['transaction']['message']['accountKeys']]
    signers_of = lambda t: keys_of(t)[:t['transaction']['message']['header']['numRequiredSignatures']]
    for k, t in txs.items():
        assert keys_of(t)[0] == (C['payer'] if k == label + '-open' else session), f'{k}: unexpected fee payer'
        assert t['meta']['fee'] == (FEE2 if k == label + '-open' else FEE1), f'{k}: unexpected fee'
    payer_signed = sorted(k for k, t in txs.items() if C['payer'] in signers_of(t))
    assert payer_signed == [label + '-open'], f'the payer signed more than the open: {payer_signed}'
    fees = sum(t['meta']['fee'] for t in txs.values()); delta = payer_after - payer_before
    created = set()
    for t in txs.values():
        created.update(created_accounts(t))
    live = {a: L.account(a)['value'] for a in sorted(created)}; live = {a: v for a, v in live.items() if v and v['lamports']}
    assert set(live) == {p['marker']}, f'unexpected live accounts after close: {sorted(set(live) - {p["marker"]})}'
    left = sum(v['lamports'] for v in live.values())
    assert left == rent_marker and -delta == fees + left, 'payer balance change != fees + marker rent'
    recovered = fund - (-delta - FEE2)      # what came back of the funding
    tests = {f'{label}-{x}' for x in ('cert-mutate', 'cert-settle', 'cert-restore', 'node-mutate', 'node-settle', 'node-restore', 'replay')} if MODE == 'evidence' else set()
    if MODE == 'evidence' and n == 1:
        tests |= {f'{label}-{x}-settle' for x in ('redirect-both', 'redirect-account', 'redirect-request')}
    prod = [k for k in names if k not in tests]
    assert len(prod) == 18 and set(tests) <= set(names), f'production path is not 18 transactions: {prod}'
    test_fees = sum(txs[k]['meta']['fee'] for k in tests)
    production = {'transactions': len(prod), 'names': prod, 'signed_by_payer': payer_signed, 'fees_lamports': fees - test_fees,
                  'payer_delta_lamports': delta + test_fees,
                  'note': 'the payment alone (open, 15 writes, the one settlement transaction, close), without the negative tests'}
    assert -production['payer_delta_lamports'] == production['fees_lamports'] + left
    payments[label] = {'settle': {k: settled[k] for k in ('signature', 'slot', 'compute_units', 'fee', 'serialized_bytes', 'explorer')},
                       'settle_margin_compute_units': CU_LIMIT - settled['compute_units'],
                       'uploads': json.loads((O / (label + '-uploads-phase.json')).read_text()),
                       'session_key': session, 'funded_lamports': fund, 'returned_lamports': recovered,
                       'production_path': production, 'transactions': len(names), 'fees_lamports': fees, 'payer_delta_lamports': delta,
                       'rent_closed_lamports': rent_closed,
                       'left_live': {a: {'owner': v['owner'], 'lamports': v['lamports'], 'role': 'nullifier marker' if a == p['marker'] else 'root page'} for a, v in live.items()},
                       'left_lamports': left, 'check_payer_delta_eq_fees_plus_left': True, 'closed': closing + [session],
                       'negatives': {name: json.loads((O / f'{label}-{name}-validation.json').read_text()) for name in ('cert', 'node')} if MODE == 'evidence' else None,
                       'wallet_timing': json.loads((O / (label + '-wallet-timing.json')).read_text()) if MODE == 'timing' else None}
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
L.write('complete', {'route': 'future-version one-transaction (summed format)', 'settled': ['transfer', 'withdrawal'],
                     'settle_compute_units': {k: v['settle']['compute_units'] for k, v in payments.items()},
                     'negative_errors': observed_errors, 'closed_per_payment': {k: v['closed'] for k, v in payments.items()},
                     'mode': MODE, 'negative_checks': [f'{l}-{x}' for l in payments for x in ('cert-settle', 'node-settle', 'replay')] if MODE == 'evidence' else [],
                     'mint': mint, 'source': source, 'destination': dest, 'fixture_witnesses_public': True, 'programs': P,
                     'upload_program': UP, 'payer': C['payer'], 'key_namespace': ns, 'payments': payments})
print(json.dumps({'settle_compute_units': {k: v['settle']['compute_units'] for k, v in payments.items()}, 'negative_errors': observed_errors}))
