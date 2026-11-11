"""Retained-key and loader rent policy. Importing this module performs no I/O."""
import base64
import json
import pathlib
import stat
import subprocess

LOADER = 'BPFLoaderUpgradeab1e11111111111111111111111'


def require_key(path, cli, expected=None):
    path = pathlib.Path(path)
    mode = path.lstat().st_mode
    if not stat.S_ISREG(mode) or stat.S_IMODE(mode) != 0o600:
        raise ValueError(f'retained key must be a regular mode 0600 file: {path}')
    public = subprocess.check_output([str(cli/'solana-keygen'), 'pubkey', str(path)], text=True).strip()
    if expected is not None and public != expected:
        raise ValueError(f'retained key public identity mismatch: {path}')
    return {'path': str(path.absolute()), 'public': public, 'mode': '0600'}


def loader_rent(address, account, payer, immutable_program=False):
    """Conservatively classify live loader accounts; never infer recoverability from a key file."""
    raw = base64.b64decode(account['data'][0])
    tag = int.from_bytes(raw[:4], 'little')
    authority = None
    kind, recovery = 'unknown', 'unestablished'
    if account['owner'] == LOADER:
        if tag == 1:
            kind, recovery = 'buffer', 'payer loader close after finalized signature reconciliation'
        elif tag == 2:
            kind, recovery = 'program', ('permanently locked' if immutable_program else 'Program stub has no loader close path; budget as locked')
        elif tag == 3:
            kind = 'programdata'
            if len(raw) < 45:
                raise ValueError('short ProgramData')
            authority = raw[12]
            recovery = 'permanently locked' if authority == 0 else 'retained upgrade authority loader close'
    from r1_devnet_release_gate import base58
    recoverable=(kind=='buffer' and len(raw)>=37 and raw[4]==1 and raw[5:37]==base58(payer)) or (kind=='programdata' and len(raw)>=45 and raw[12]==1 and raw[13:45]==base58(payer))
    return {'address': address, 'lamports': account['lamports'], 'kind': kind,
            'recovery': recovery, 'recovery_public_destination': payer,
            'authority_option': authority,
            'locked_lamports': account['lamports'] if kind=='program' or recovery=='permanently locked' else 0,
            'recoverable_lamports': account['lamports'] if recoverable else 0,
            'recoverability_requires_authority_check': kind!='program' and recovery!='permanently locked' and not recoverable}


def close_failed_buffer(cli, url, payer_key, payer, buffer, fetch, output):
    """Keep every key. Close only a confirmed buffer under the checked payer authority."""
    account = fetch(buffer)['value']
    if account is None or account['lamports'] == 0:
        return {'buffer': buffer, 'remaining_lamports': 0, 'key_retained': True}
    raw = base64.b64decode(account['data'][0])
    # Compare public authority bytes without opening the payer key.
    from r1_devnet_release_gate import base58
    if (account['owner'] != LOADER or len(raw) < 37 or
            int.from_bytes(raw[:4], 'little') != 1 or raw[4] != 1 or raw[5:37] != base58(payer)):
        raise ValueError('buffer authority/type mismatch; retain keys and inspect')
    command = [str(cli/'solana'), '--url', url, '--keypair', str(payer_key),
               '--commitment', 'finalized', '--output', 'json', 'program', 'close',
               buffer, '--recipient', payer]
    result = subprocess.run(command, text=True, capture_output=True)
    output('buffer-refund', {'command': command, 'exit': result.returncode,
                            'stdout': result.stdout, 'stderr': result.stderr,
                            'recipient': payer, 'key_retained': True})
    if result.returncode:
        raise RuntimeError('buffer refund failed; retain keys')
    remaining = fetch(buffer)['value']
    if remaining is not None and remaining['lamports'] != 0:
        raise RuntimeError('buffer refund not finalized/zero; retain keys')
    return {'buffer': buffer, 'remaining_lamports': 0, 'recipient': payer, 'key_retained': True}


def created_accounts(transaction):
    """Newly funded accounts from finalized metadata, including PDA CPI creations."""
    meta = transaction['meta']
    if meta['err']:
        return []
    keys = transaction['transaction']['message']['accountKeys']
    return [(key if isinstance(key, str) else key['pubkey'])
            for key, before, after in zip(keys, meta['preBalances'], meta['postBalances'])
            if before == 0 and after > 0]


def state_rent(address, account, payer, token_authority=None):
    row= {'address': address, 'owner': account['owner'], 'lamports': account['lamports'],
            'data_bytes': len(base64.b64decode(account['data'][0])),
            'recovery': 'no demonstrated close path; budget as locked',
            'recovery_public_destination': payer,
            'keys_retained': True, 'recoverable_lamports': 0, 'locked_lamports': account['lamports']}
    raw=base64.b64decode(account['data'][0])
    if token_authority and account['owner']=='TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA' and len(raw)==165:
        from r1_devnet_release_gate import base58
        if raw[32:64]==base58(token_authority) and raw[129:133]==bytes(4):
            row.update(recovery='SPL Token CloseAccount after token balance zero',
                       recovery_authority=token_authority, token_balance=int.from_bytes(raw[64:72],'little'),
                       recoverable_lamports=account['lamports'],locked_lamports=0)
    return row
