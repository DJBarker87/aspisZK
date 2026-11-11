"""Offline test of PIN2_recover.inspect: public fixtures, no RPC, no keys."""
import base64, unittest
import PIN2_recover as r
import PIN2_seed_accounts as s

PAYER = s.b58encode(b'\x11' * 32); UP = s.b58encode(b'\x22' * 32); VER = s.b58encode(b'\x33' * 32)
TAG = '00112233445566778899aabbccddee'


class Inspect(unittest.TestCase):
    def test_fixed_order_and_classification(self):
        lay = s.layout(PAYER, UP, VER, TAG)
        live = {lay['proof_accounts'][3]: {'owner': UP, 'executable': False, 'lamports': 10, 'data': [base64.b64encode(b'x' * 5).decode(), 'base64']},
                lay['statement']['address']: {'owner': s.b58encode(b'\x44' * 32), 'executable': False, 'lamports': 7, 'data': ['', 'base64']},
                lay['checkpoint']['address']: {'owner': VER, 'executable': False, 'lamports': 9, 'data': [base64.b64encode(bytes(1768)).decode(), 'base64']},
                lay['negative_checkpoint']['address']: {'owner': VER, 'executable': False, 'lamports': 9, 'data': [base64.b64encode(bytes(10)).decode(), 'base64']}}
        rows = r.inspect(lay, live.get, UP, VER)
        self.assertEqual([x['seed'][:2] for x in rows], ['p0', 'p1', 'p2', 'p3', 'p4', 'p5', 'p6', 'p7', 's0', 'c0', 'n0'])
        state = {x['seed'][:2]: x['state'] for x in rows}
        self.assertEqual(state['p3'], 'closable'); self.assertEqual(state['p0'], 'absent')
        self.assertEqual(state['s0'], 'unexpected'); self.assertEqual(state['c0'], 'closable'); self.assertEqual(state['n0'], 'unexpected')


if __name__ == '__main__':
    unittest.main()
