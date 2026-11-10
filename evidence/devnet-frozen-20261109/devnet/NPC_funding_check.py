"""NPC_ B1 read-only writer preflight and funding gate (NDZ_funding_check.py adapted to two new programs).
Generates no signature. Funding rule (lead, 2026-11-10): pass if the balance covers the conservative
simultaneous peak; otherwise pass only if expected spend plus a 3 SOL margin fits, and record that basis."""
import base64, hashlib, json, pathlib, subprocess, sys
from r1_devnet_rpc import rpc
from r1_devnet_policy import require_key
C = json.load(open(sys.argv[1])); assert C['rpc_url'] == 'https://api.devnet.solana.com'
url = C['rpc_url']; cli = pathlib.Path(C['cli_dir']); keys = pathlib.Path(C['key_dir'])
assert not list(keys.glob(C['key_namespace'] + '-*')), 'retained fixture namespace already exists: inspect and resume, never replace keys'
retained = [require_key(C['payer_key'], cli, C['payer']), require_key(keys / 'verifier.json', cli, C['programs']['verifier']),
            require_key(keys / 'pool.json', cli, C['programs']['pool'])]
assert rpc(url, 'getGenesisHash', []) == C['genesis_hash']
buffers = json.loads(subprocess.check_output([str(cli / 'solana'), '--keypair', C['payer_key'], '--url', url, '--output', 'json', 'program', 'show', '--buffers', '--buffer-authority', C['payer']]))
assert buffers == {'buffers': []}, 'pre-existing payer buffers: inspect and recover first'
art = C['release_artifacts']
for role, n, h in [('devnet_verifier', 1563728, '2331ad8a2d97439a30329328c51f619a6b13be97e260ab1e1fd8aab22cb996ea'), ('pool', 345648, 'e0e49c344d35575116c0359450315ea4334bfb03006551727f67c04a8cfe09dc')]:
    elf = pathlib.Path(art[role]['path']).read_bytes(); assert len(elf) == n and hashlib.sha256(elf).hexdigest() == art[role]['sha256'] == h, role
for role in ('verifier', 'pool'):
    assert rpc(url, 'getAccountInfo', [C['programs'][role], {'encoding': 'base64', 'commitment': 'finalized'}])['value'] is None, role + ' address exists: inspect, do not redeploy'
dependencies = {}
for role, address in (('registry', C['programs']['registry']), ('carrier', C['carrier'])):
    show = json.loads(subprocess.check_output([str(cli / 'solana'), '--keypair', C['payer_key'], '--url', url, '--output', 'json', 'program', 'show', address]))
    value = rpc(url, 'getAccountInfo', [show['programdataAddress'], {'encoding': 'base64', 'commitment': 'finalized'}])
    raw = base64.b64decode(value['value']['data'][0]); spec = art[role]; payload = raw[45:]
    assert value['value']['owner'] == 'BPFLoaderUpgradeab1e11111111111111111111111' and int.from_bytes(raw[:4], 'little') == 3
    assert len(payload) >= spec['bytes'] and hashlib.sha256(payload[:spec['bytes']]).hexdigest() == spec['sha256'] and not any(payload[spec['bytes']:])
    if role == 'registry': assert raw[12] == 0
    dependencies[role] = {'show': show, 'slot': value['context']['slot'], 'elf_sha256': spec['sha256'], 'immutable': raw[12] == 0}
features = {}
for name, address in [('txv1', 'txv1aq4pp281K9um3tnPgkfX8UqtFT6wcVW3hNezGLL'), ('disable_legacy_sbpf_deployment', 'B8JJXCy5amZyWG9r7EnUYLwzXSXTxG7GZ1qZ1qggo83g')]:
    account = rpc(url, 'getAccountInfo', [address, {'encoding': 'base64', 'commitment': 'finalized'}]); value = account['value']; active = False
    if value:
        raw = base64.b64decode(value['data'][0])
        assert value['owner'] == 'Feature111111111111111111111111111111111111' and len(raw) == 9, 'unrecognized feature account'
        active = raw[0] == 1 and int.from_bytes(raw[1:9], 'little') <= account['context']['slot']
    features[name] = {'address': address, 'active': active, 'account': account}
assert features['txv1']['active'], 'TxV1 inactive: STOP'
assert not features['disable_legacy_sbpf_deployment']['active'], 'legacy-SBPF deployment disabled: frozen ELFs cannot be newly deployed: STOP'
ledger_source = pathlib.Path(sys.argv[3]); ledger = json.load(open(ledger_source))  # NDZ's devnet fixture rent ledger (28 accounts)
sizes = {36, 345648 + 37, 345648 + 45, 1563728 + 37, 1563728 + 45} | {x['data_bytes'] for x in ledger}
rents = {n: rpc(url, 'getMinimumBalanceForRentExemption', [n, {'commitment': 'finalized'}]) for n in sorted(sizes)}
fixtures = sum(rents[x['data_bytes']] for x in ledger); locked_fixtures = sum(rents[x['data_bytes']] for x in ledger if x['locked_lamports'])
stub = rents[36]; pool_buf, pool_pd = rents[345685], rents[345693]; ver_buf, ver_pd = rents[1563765], rents[1563773]
fee_reserve = 100000000; fee_estimate = 30000000; margin = 3000000000
simultaneous = pool_buf + pool_pd + stub + ver_buf + ver_pd + stub + fixtures + fee_reserve
sequential = max(pool_buf + pool_pd + stub, pool_pd + stub + ver_buf + ver_pd + stub) + fixtures + fee_reserve
expected = pool_pd + stub + ver_pd + stub + fixtures + fee_estimate
balance = rpc(url, 'getBalance', [C['payer'], {'commitment': 'finalized'}])
b = balance['value']
basis = 'conservative_simultaneous_peak' if b >= simultaneous else ('expected_plus_3_SOL_margin (lead rule 2026-11-10)' if b >= expected + margin else None)
result = {'features': features, 'ledger_source': str(ledger_source), 'retained_keys': retained, 'dependencies': dependencies, 'rpc_url': url, 'balance': balance,
          'rent_quotes': rents, 'fixture_rent_lamports': fixtures, 'fixture_locked_budget_lamports': locked_fixtures,
          'pool_programdata_recoverable_lamports': pool_pd, 'verifier_permanently_locked_lamports': ver_pd + stub, 'stubs_locked_lamports': 2 * stub,
          'permanent_locked_budget_lamports': ver_pd + 2 * stub + locked_fixtures, 'fee_reserve_lamports': fee_reserve, 'fee_estimate_lamports': fee_estimate,
          'conservative_simultaneous_peak_lamports': simultaneous, 'conservative_sequential_peak_lamports': sequential,
          'expected_spend_lamports': expected, 'margin_lamports': margin,
          'headroom_vs_simultaneous': b - simultaneous, 'headroom_vs_sequential': b - sequential, 'headroom_vs_expected_plus_margin': b - expected - margin,
          'funding_basis': basis, 'funding_pass': basis is not None, 'signatures_generated': 0}
pathlib.Path(sys.argv[2]).write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in ('retained_keys', 'rent_quotes', 'features', 'dependencies')}, indent=2))
print('features', {k: v['active'] for k, v in features.items()})
assert result['funding_pass'], 'insufficient funding under both bases: STOP'
