"""PIN2 seeded per-payment accounts. Importing this module performs no I/O.

Every per-payment account is created with the system program's
CreateAccountWithSeed(base = payer, seed, owner) and has no private key:

  proof attempt k (0..8)  seed "p{k}" + tag   owner = aspis-upload program
  statement               seed "s0"   + tag   owner = aspis-upload program
  verifier checkpoint     seed "c0"   + tag   owner = verifier program
  negative checkpoint     seed "n0"   + tag   owner = verifier (test runs only)

tag = 30 lowercase hex characters (15 bytes from os.urandom), drawn once per
payment and retained in a private 0600 record before anything is proved or
funded. The eight proof-attempt addresses are the prover's public mask nonces
(Client64 route); they are distinct because their seeds differ, and fresh
because the tag is new per payment; proof_plan_seeded still checks that all
eight are absent on chain before invoking the prover.

Addresses are derived here (sha256(base || seed || owner), the
Pubkey::create_with_seed rule) and independently by the Rust planner
(pin2_layout); check_layout requires the two to agree.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import time

import Client64_proof_accounts as c64

ROUTE = 'pin2-seeded-upload-v1'
CAP = 8
TAG_RE = re.compile(r'[0-9a-f]{30}')
PDA_MARKER = b'ProgramDerivedAddress'


def b58decode(s):
    n = 0
    for ch in s:
        n = n * 58 + c64.ALPHABET.index(ch)
    raw = b'\0' * (len(s) - len(s.lstrip('1'))) + n.to_bytes((n.bit_length() + 7) // 8, 'big')
    if len(raw) != 32:
        raise ValueError('not a 32-byte address')
    return raw


def b58encode(b):
    n = int.from_bytes(b, 'big')
    out = ''
    while n:
        n, r = divmod(n, 58)
        out = c64.ALPHABET[r] + out
    return '1' * (len(b) - len(b.lstrip(b'\0'))) + out


def derive(base, seed, owner):
    """Pubkey::create_with_seed with the SDK's rules (<= 32 bytes, UTF-8, no PDA-marker owner)."""
    raw_seed = seed.encode('utf-8')
    if not 1 <= len(raw_seed) <= 32:
        raise ValueError('seed must be 1..=32 bytes')
    owner_raw = b58decode(owner)
    if owner_raw.endswith(PDA_MARKER):
        raise ValueError('illegal owner')
    return b58encode(hashlib.sha256(b58decode(base) + raw_seed + owner_raw).digest())


def seed(role, index, tag):
    if not TAG_RE.fullmatch(tag) or role not in 'pscn' or not 0 <= index < CAP:
        raise ValueError('bad seed parameters')
    return f'{role}{index}{tag}'


def layout(payer, upload, verifier, tag):
    proof = [{'seed': seed('p', k, tag), 'address': derive(payer, seed('p', k, tag), upload), 'owner': upload}
             for k in range(CAP)]
    one = lambda role, owner: {'seed': seed(role, 0, tag), 'address': derive(payer, seed(role, 0, tag), owner), 'owner': owner}
    keys = [p['address'] for p in proof]
    if len(set(keys)) != CAP:
        raise ValueError('duplicate attempt address')
    return {'route': ROUTE, 'base': payer, 'upload_program': upload, 'verifier': verifier, 'pin2_tag': tag,
            'proof_attempts': proof, 'proof_accounts': keys, 'statement': one('s', upload),
            'checkpoint': one('c', verifier), 'negative_checkpoint': one('n', verifier)}


def check_layout(planned, payer, upload, verifier, tag):
    """The Rust planner's layout must equal the independent Python derivation."""
    mine = layout(payer, upload, verifier, tag)
    if planned != mine:
        raise ValueError('planner layout differs from the Python derivation')
    return mine


def allocate(path, identity, entropy=os.urandom):
    """Create (exclusively) or reload the private per-payment seed record."""
    path = Path(path)
    if path.exists():
        c64.private_file(path)
        record = json.loads(path.read_text())
        if record.get('identity') != identity or not TAG_RE.fullmatch(record.get('pin2_tag', '')):
            raise ValueError('retained seed record identity changed; inspect manually')
        return record
    tag = entropy(15).hex()
    if not TAG_RE.fullmatch(tag):
        raise ValueError('entropy source returned the wrong length')
    record = {'route': ROUTE, 'identity': identity, 'pin2_tag': tag, 'created_unix': time.time()}
    fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    with os.fdopen(fd, 'w') as stream:
        json.dump(record, stream, sort_keys=True, indent=2)
        stream.write('\n')
        stream.flush()
        os.fsync(stream.fileno())
    c64.sync_dir(path.parent)
    return record


def proof_plan_seeded(root, identity, lay, prepare, invoke, absent, legacy_plan=None):
    """Client64 proof_plan with seed-derived attempt accounts instead of keypairs.

    Returns (plan, attempt record) where the record holds the selected attempt's
    seed and address. The attempt files under root are public records (seed,
    address), written 0600 only to reuse the Client64 manifest discipline.
    """
    def generate(path):
        k = int(re.fullmatch(r'attempt-([0-7])\.json', Path(path).name).group(1))
        entry = lay['proof_attempts'][k]
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, 'w') as stream:
            json.dump({'route': ROUTE, 'index': k, **entry}, stream, sort_keys=True)
            stream.flush()
            os.fsync(stream.fileno())
        return entry['address']

    def public(path):
        c64.private_file(Path(path))
        rec = json.loads(Path(path).read_text())
        if derive(lay['base'], rec['seed'], rec['owner']) != rec['address'] or rec['owner'] != lay['upload_program']:
            raise ValueError('attempt record does not derive')
        return rec['address']

    plan, path = c64.proof_plan(root, identity, prepare, invoke, absent, generate, public, legacy_plan)
    rec = json.loads(Path(path).read_text())
    if rec['address'] != plan['proof_account'] or rec['index'] != plan['attempt_index']:
        raise ValueError('selected attempt record mismatch')
    return plan, rec
