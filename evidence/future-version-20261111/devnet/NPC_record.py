"""NPC_ per-transaction recorder for the local B2 run. Read-only RPC; never opens key files.

npc_pre is called after signing and before simulation/submission. It snapshots every
account named by the instructions (fee payer, program ids, instruction accounts).
npc_post is called after finalized metadata is available. It snapshots the same
accounts at finalized commitment, derives signer/writable flags from the landed
message header, and checks that no other signature touched any writable account
between the two snapshots. One file per transaction: <name>-recording.json.
"""
import base64, json, time
from r1_devnet_rpc import rpc


def _snapshot(url, keys, commitment):
    out, slot = [], None
    for i in range(0, len(keys), 100):
        r = rpc(url, 'getMultipleAccounts', [keys[i:i + 100], {'encoding': 'base64', 'commitment': commitment}])
        slot = r['context']['slot'] if slot is None else min(slot, r['context']['slot'])
        for k, v in zip(keys[i:i + 100], r['value']):
            if v is None:
                out.append({'key': k, 'exists': False})
            else:
                out.append({'key': k, 'exists': True, 'owner': v['owner'], 'lamports': v['lamports'],
                            'executable': v['executable'], 'rent_epoch': v.get('rentEpoch'),
                            'space': v.get('space'), 'data_base64': v['data'][0]})
    return {'commitment': commitment, 'context_slot': slot, 'accounts': out}


def npc_pre(url, out_dir, name, attempt, ixs, signed, payer, negative):
    keys = [payer]
    for ix in ixs:
        for k in [ix['program']] + [a[0] for a in ix['accounts']]:
            if k not in keys:
                keys.append(k)
    state = {'name': name, 'attempt': attempt, 'negative': negative, 'signature': signed['signature'],
             'serialized_transaction_hex': signed['hex'], 'serialized_bytes': signed['bytes'],
             'instructions': [{'program': ix['program'],
                               'accounts': [{'key': a[0], 'is_signer': bool(a[1]), 'is_writable': bool(a[2])} for a in ix['accounts']],
                               'data_hex': ix['data']} for ix in ixs],
             'keys': keys, 'pre': _snapshot(url, keys, 'processed'), 'pre_unix': time.time()}
    (out_dir / f'{name}-attempt-{attempt}-pre.json').write_text(json.dumps(state) + '\n')
    return state


def npc_post(url, out_dir, name, state, tx):
    sig = state['signature']
    msg = tx['transaction']['message']
    mkeys = [k if isinstance(k, str) else k['pubkey'] for k in msg['accountKeys']]
    h = msg['header']
    nsig, ro_sig, ro_unsig = h['numRequiredSignatures'], h['numReadonlySignedAccounts'], h['numReadonlyUnsignedAccounts']
    flags = []
    for i, k in enumerate(mkeys):
        signer = i < nsig
        writable = (i < nsig - ro_sig) if signer else (i < len(mkeys) - ro_unsig)
        flags.append({'key': k, 'is_signer': signer, 'is_writable': writable})
    loaded = tx['meta'].get('loadedAddresses') or {}
    assert not loaded.get('writable') and not loaded.get('readonly'), 'address lookup tables not expected'
    assert set(mkeys) == set(state['keys']), 'message keys differ from instruction keys'
    post = _snapshot(url, state['keys'], 'finalized')
    lo, hi = state['pre']['context_slot'], post['context_slot']
    foreign = {}
    for f in flags:
        if not f['is_writable']:
            continue
        rows = rpc(url, 'getSignaturesForAddress', [f['key'], {'limit': 100, 'commitment': 'finalized'}])
        other = [r['signature'] for r in rows if lo <= r['slot'] <= hi and r['signature'] != sig]
        if other:
            foreign[f['key']] = other
    parsed = rpc(url, 'getTransaction', [sig, {'encoding': 'jsonParsed', 'commitment': 'finalized', 'maxSupportedTransactionVersion': 1}])
    rec = dict(state)
    rec.update({'post': post, 'message_account_flags': flags, 'tx_slot': tx['slot'],
                'clock': {'slot': tx['slot'], 'unix_timestamp_from_blockTime': tx.get('blockTime'),
                          'epoch_schedule': rpc(url, 'getEpochSchedule', []),
                          'note': 'Clock.slot equals the bank slot of the landed transaction; blockTime is the bank Clock.unix_timestamp. The Clock sysvar account at that slot is not retrievable afterwards over RPC.'},
                'isolation': {'pre_context_slot': lo, 'post_context_slot': hi, 'writable_accounts_checked': sum(f['is_writable'] for f in flags),
                              'foreign_signatures': foreign, 'isolated': not foreign},
                'meta': tx['meta'], 'transaction_json': tx, 'transaction_jsonParsed': parsed})
    (out_dir / f'{name}-recording.json').write_text(json.dumps(rec) + '\n')
    return rec
