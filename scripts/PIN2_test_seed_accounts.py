"""Offline tests for PIN2_seed_accounts: public fixtures only, no keys, prover or RPC."""
import copy
import json
from pathlib import Path
import tempfile
import unittest
import PIN2_seed_accounts as s

PAYER = s.b58encode(bytes([0x11]) * 32)
UPLOAD = s.b58encode(bytes([0x22]) * 32)
VERIFIER = s.b58encode(bytes([0x33]) * 32)
TAG = '00112233445566778899aabbccddee'


class Derivation(unittest.TestCase):
    def test_golden_vectors_shared_with_rust_planner(self):
        lay = s.layout(PAYER, UPLOAD, VERIFIER, TAG)
        self.assertEqual(lay['proof_accounts'][0], '6nPTTqm7ja3XgjsPt6kXXwtiEVH5nx2EVjdPuUExBreU')
        self.assertEqual(lay['proof_accounts'][7], '5Skhkx5FKaMHqfNw6HrJANBma1MnnkDWC7VKKupX9Bni')
        self.assertEqual(lay['statement']['address'], '6JJqjatYYLJpjWwaTfjwVJgvyufrs56JLPVhkywQUiW8')
        self.assertEqual(lay['checkpoint']['address'], '6z6Dya2a6xXCAmNfVVwHdkf8QKhYxUEcdhhBN9axnBTY')
        self.assertEqual(len(set(lay['proof_accounts'])), 8)
        self.assertTrue(all(len(a['seed']) == 32 for a in lay['proof_attempts']))

    def test_rules(self):
        for bad in ['', 'x' * 33]:
            with self.assertRaises(ValueError):
                s.derive(PAYER, bad, UPLOAD)
        with self.assertRaises(ValueError):
            s.derive(PAYER, 'a', s.b58encode(b'\1' * 11 + s.PDA_MARKER))
        for tag in ['', TAG.upper(), TAG[:-1], TAG + '0']:
            with self.assertRaises(ValueError):
                s.layout(PAYER, UPLOAD, VERIFIER, tag)
        planned = s.layout(PAYER, UPLOAD, VERIFIER, TAG)
        s.check_layout(copy.deepcopy(planned), PAYER, UPLOAD, VERIFIER, TAG)
        planned['checkpoint']['address'] = planned['statement']['address']
        with self.assertRaises(ValueError):
            s.check_layout(planned, PAYER, UPLOAD, VERIFIER, TAG)


class Records(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.dir = Path(self.temp.name)

    def test_allocate_exclusive_and_stable(self):
        ident = {'label': 'transfer', 'payer': PAYER}
        r1 = s.allocate(self.dir / 'seeds.json', ident, entropy=lambda n: bytes(range(n)))
        self.assertEqual(r1['pin2_tag'], bytes(range(15)).hex())
        self.assertEqual((self.dir / 'seeds.json').stat().st_mode & 0o777, 0o600)
        r2 = s.allocate(self.dir / 'seeds.json', ident, entropy=lambda n: b'\xff' * n)
        self.assertEqual(r1, r2)
        with self.assertRaises(ValueError):
            s.allocate(self.dir / 'seeds.json', {**ident, 'label': 'withdrawal'})
        with self.assertRaises(ValueError):
            s.allocate(self.dir / 'short.json', ident, entropy=lambda n: b'\0' * (n - 1))

    def test_distinct_payments_get_distinct_nonces(self):
        a = s.allocate(self.dir / 'a.json', {'n': 0})
        b = s.allocate(self.dir / 'b.json', {'n': 1})
        la = s.layout(PAYER, UPLOAD, VERIFIER, a['pin2_tag'])
        lb = s.layout(PAYER, UPLOAD, VERIFIER, b['pin2_tag'])
        self.assertFalse(set(la['proof_accounts']) & set(lb['proof_accounts']))

    def test_proof_plan_seeded_selects_attempt_record(self):
        lay = s.layout(PAYER, UPLOAD, VERIFIER, TAG)
        ident = {'action': 'prove', 'pool': PAYER, 'verifier': VERIFIER, 'checkpoint': UPLOAD,
                 'public_account': lay['statement']['address'], 'verifier_checkpoint': lay['checkpoint']['address']}
        seen = []

        def invoke(q):
            seen.append(q)
            self.assertEqual(q['proof_accounts'], lay['proof_accounts'])
            d = Path(q['proof_dir']); d.mkdir(mode=0o700)
            (d / 'proof.bin').write_bytes(b'p'); (d / 'statement.bin').write_bytes(b's')
            key = q['proof_accounts'][2]
            return {'client_route': 'selected64-proof-account-v1', 'attempts': 3, 'attempt_index': 2, 'proof_account': key,
                    'stage1': {'program': VERIFIER, 'data': '030a', 'accounts': [[key, False, False], [q['public_account'], False, False], [q['verifier_checkpoint'], False, True]]},
                    'settle': {'program': PAYER, 'data': '', 'accounts': [[UPLOAD, False, False], [UPLOAD, False, False]] + [[UPLOAD, False, False]] * 8 + [[key, False, False], [q['verifier_checkpoint'], False, False]]}}
        root = self.dir / 'private'
        plan, rec = s.proof_plan_seeded(root, ident, lay, lambda: {}, invoke, lambda k: True)
        self.assertEqual((rec['index'], rec['seed'], rec['address']), (2, 'p2' + TAG, lay['proof_accounts'][2]))
        plan2, rec2 = s.proof_plan_seeded(root, ident, lay, lambda: {}, None, None)  # resume: no invocation
        self.assertEqual((plan, rec), (plan2, rec2))
        self.assertEqual(len(seen), 1)
        # Any pre-existing attempt address refuses the fresh invocation.
        with self.assertRaises(ValueError):
            s.proof_plan_seeded(self.dir / 'p2', ident, lay, lambda: {}, invoke, lambda k: k != lay['proof_accounts'][5])
        # Tampered attempt record fails the derivation check on resume.
        rec_path = root / 'attempt-4.json'
        data = json.loads(rec_path.read_text()); data['seed'] = 'p5' + TAG
        rec_path.chmod(0o600); rec_path.write_text(json.dumps(data))
        with self.assertRaises(ValueError):
            s.proof_plan_seeded(root, ident, lay, lambda: {}, None, None)


if __name__ == '__main__':
    unittest.main()
