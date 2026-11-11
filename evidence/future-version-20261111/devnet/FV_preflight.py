#!/usr/bin/env python3
"""Future-version one-transaction run: read-only preflight and funding gate (PIN2_preflight.py adapted).
Generates no signature and opens no key bytes.

usage: FV_preflight.py FV_config.json OUT.json

Checks: genesis; payer key file (0600, public key); key namespace unused; the one-transaction
verifier and the aspis-upload program are deployed (loader-v3) with ProgramData payloads equal to
the pinned artifacts, the verifier immutable (the registry requires it); the existing Pool payload
equals its pin; the registry is immutable at its pin; TxV1 is active. Funding: the payer must cover
the fixture rent (the PIN2 run left 138,993,880 lamports live; 150,000,000 is budgeted, scaled by
the cluster's rent), one payment's refundable accounts at a time (proof and checkpoint), the fees
of both payments, the fixtures and the cleanup, and a 0.1 SOL reserve.
"""
import base64, hashlib, json, pathlib, sys
from r1_devnet_rpc import rpc
from r1_devnet_policy import require_key
from PIN2_seed_accounts import b58encode

C = json.load(open(sys.argv[1])); url = C['rpc_url']; cli = pathlib.Path(C['cli_dir'])
assert 'carrier' not in C
keys = pathlib.Path(C['key_dir'])
assert not list(keys.glob(C['key_namespace'] + '-*')), 'key namespace already used: resume or pick a fresh namespace'
retained = [require_key(C['payer_key'], cli, C['payer'])]
assert rpc(url, 'getGenesisHash', []) == C['genesis_hash']


def programdata(program):
    v = rpc(url, 'getAccountInfo', [program, {'encoding': 'base64', 'commitment': 'finalized'}])['value']
    assert v and v['owner'] == 'BPFLoaderUpgradeab1e11111111111111111111111' and v['executable'], f'{program}: not a deployed loader-v3 program'
    raw = base64.b64decode(v['data'][0]); assert int.from_bytes(raw[:4], 'little') == 2
    pd = b58encode(raw[4:36])
    w = rpc(url, 'getAccountInfo', [pd, {'encoding': 'base64', 'commitment': 'finalized'}])
    d = base64.b64decode(w['value']['data'][0]); assert int.from_bytes(d[:4], 'little') == 3
    return pd, d, w['context']['slot'], w['value']['lamports']


# `solana program deploy --final` revokes the authority in a transaction after the deployment. Both are read
# here at finalized commitment, so wait (bounded) until the finalized view shows the verifier without an authority.
import time
for _ in range(45):
    try:
        if programdata(C['programs']['verifier'])[1][12] == 0:
            break
    except AssertionError:
        pass
    time.sleep(2)
art = C['release_artifacts']; deps = {}
for role, program in [('devnet_verifier', C['programs']['verifier']), ('pool', C['programs']['pool']),
                      ('registry', C['programs']['registry']), ('upload', C['upload_program'])]:
    spec = art[role]
    local = pathlib.Path(spec['path']).read_bytes()
    assert len(local) == spec['bytes'] and hashlib.sha256(local).hexdigest() == spec['sha256'], f'{role}: local artifact differs from pin'
    pd, d, slot, lamports = programdata(program); payload = d[45:]
    assert hashlib.sha256(payload[:spec['bytes']]).hexdigest() == spec['sha256'] and not any(payload[spec['bytes']:]), f'{role}: deployed payload differs'
    deps[role] = {'program': program, 'programdata': pd, 'slot': slot, 'immutable': d[12] == 0, 'payload_bytes': len(payload),
                  'payload_sha256': hashlib.sha256(payload).hexdigest(), 'programdata_lamports': lamports,
                  'authority': None if d[12] == 0 else b58encode(d[13:45])}
assert deps['devnet_verifier']['immutable'], 'registry accepts only an immutable verifier'
# The registry hashes the whole payload: it must equal the scheduled hash, so no padding is allowed.
assert deps['devnet_verifier']['payload_sha256'] == art['devnet_verifier']['sha256'], 'verifier ProgramData carries padding: the scheduled hash would differ'
assert deps['registry']['immutable'] and deps['upload']['immutable']
feat = rpc(url, 'getAccountInfo', ['txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL', {'encoding': 'base64', 'commitment': 'finalized'}])
raw = base64.b64decode(feat['value']['data'][0]) if feat['value'] else b''
assert len(raw) == 9 and raw[0] == 1 and int.from_bytes(raw[1:9], 'little') <= feat['context']['slot'], 'TxV1 inactive: STOP'
sizes = [1768, 56503]
rent = {n: rpc(url, 'getMinimumBalanceForRentExemption', [n, {'commitment': 'finalized'}]) for n in sizes}
per_byte = rent[1768] // (1768 + 128)
fixtures = 150_000_000 * per_byte // 5080 + 1
per_payment_refundable = rent[56503] + rent[1768]
fees = 2 * 30 * 15000 + 30 * 15000 + 5 * 15000   # <= 30 transactions per payment, ~30 fixture transactions, cleanup
reserve = 100_000_000
need = fixtures + per_payment_refundable + fees + reserve
balance = rpc(url, 'getBalance', [C['payer'], {'commitment': 'finalized'}])['value']
out = {'retained_keys': retained, 'dependencies': deps, 'rent_quotes': rent, 'rent_lamports_per_byte': per_byte, 'fixture_rent_budget_lamports': fixtures,
       'per_payment_refundable_peak_lamports': per_payment_refundable, 'fee_budget_lamports': fees, 'reserve_lamports': reserve,
       'need_lamports': need, 'balance_lamports': balance, 'headroom_lamports': balance - need, 'funding_pass': balance >= need,
       'signatures_generated': 0}
pathlib.Path(sys.argv[2]).write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps({k: v for k, v in out.items() if k not in ('retained_keys', 'rent_quotes')}, indent=2))
assert out['funding_pass'], 'insufficient funding: STOP'
