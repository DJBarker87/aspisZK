import base64
import pathlib
import tempfile
import unittest
from unittest.mock import patch
from r1_devnet_policy import require_key, loader_rent, close_failed_buffer, created_accounts, LOADER
from r1_devnet_release_gate import base58

PAYER='CVZJcAv97von8njTJSyLVQ9X33NAKQYbEXFKnAYvst9t'
def account(raw,owner=LOADER):
    return {'owner':owner,'lamports':123,'data':[base64.b64encode(raw).decode(),'base64']}

class Policy(unittest.TestCase):
    def test_missing_or_nonprivate_key_fails_before_keytool(self):
        with tempfile.TemporaryDirectory() as root, patch('subprocess.check_output') as public:
            path=pathlib.Path(root)/'public-test-fixture';path.write_text('public fixture only');path.chmod(0o644)
            with self.assertRaises(ValueError):require_key(path,pathlib.Path('/cli'))
            with self.assertRaises(FileNotFoundError):require_key(path.parent/'missing',pathlib.Path('/cli'))
            public.assert_not_called()
    def test_public_identity_must_match(self):
        with tempfile.TemporaryDirectory() as root, patch('subprocess.check_output',return_value=PAYER+'\n'):
            path=pathlib.Path(root)/'public-test-fixture';path.write_text('public fixture only');path.chmod(0o600)
            self.assertEqual(require_key(path,pathlib.Path('/cli'),PAYER)['public'],PAYER)
            with self.assertRaises(ValueError):require_key(path,pathlib.Path('/cli'),'wrong')
    def test_immutable_rent_is_locked(self):
        row=loader_rent('pd',account((3).to_bytes(4,'little')+bytes(41)),PAYER)
        self.assertEqual(row['recovery'],'permanently locked')
    def test_wrong_buffer_authority_never_closes(self):
        with patch('subprocess.run') as run:
            with self.assertRaises(ValueError):close_failed_buffer(pathlib.Path('/cli'),'http://127.0.0.1:1','key',PAYER,'buffer',lambda _: {'value':account((1).to_bytes(4,'little')+b'\1'+bytes(32))},lambda *args:None)
            run.assert_not_called()
    def test_refund_is_finalized_and_zero_checked(self):
        values=iter([{'value':account((1).to_bytes(4,'little')+b'\1'+base58(PAYER))},{'value':None}])
        with patch('subprocess.run') as run:
            run.return_value.returncode=0;run.return_value.stdout='public refund signature';run.return_value.stderr=''
            result=close_failed_buffer(pathlib.Path('/cli'),'http://127.0.0.1:1','key',PAYER,'buffer',lambda _:next(values),lambda *args:None)
            self.assertEqual(result['remaining_lamports'],0)
            self.assertIn('finalized',run.call_args.args[0]);self.assertIn(PAYER,run.call_args.args[0])
    def test_cpi_creation_included_but_failed_transaction_excluded(self):
        tx={'meta':{'err':None,'preBalances':[100,0],'postBalances':[90,10]},'transaction':{'message':{'accountKeys':['payer','pda']}}}
        self.assertEqual(created_accounts(tx),['pda']);tx['meta']['err']='failure'
        self.assertEqual(created_accounts(tx),[])

if __name__=='__main__':unittest.main()
