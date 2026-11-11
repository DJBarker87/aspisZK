import ast
import types
import base64
import pathlib
import tempfile
import unittest
from unittest.mock import patch
from r1_devnet_policy import require_key, loader_rent, close_failed_buffer, created_accounts, state_rent, LOADER
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
    def test_program_stub_is_not_promised_as_refundable_before_finalization(self):
        row=loader_rent('program',account((2).to_bytes(4,'little')+bytes(32)),PAYER)
        self.assertEqual(row['locked_lamports'],123)
        self.assertEqual(row['recoverable_lamports'],0)
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
    def test_only_retained_token_owner_marks_state_rent_recoverable(self):
        raw=bytearray(165);raw[32:64]=base58(PAYER)
        token=account(raw,'TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA')
        self.assertEqual(state_rent('token',token,PAYER,PAYER)['recoverable_lamports'],123)
        raw[129:133]=(1).to_bytes(4,'little');token=account(raw,'TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA')
        self.assertEqual(state_rent('token',token,PAYER,PAYER)['recoverable_lamports'],0)
    def test_transaction_metadata_is_required_and_can_arrive_late(self):
        tree=ast.parse(pathlib.Path(__file__).with_name('r1_devnet_deploy_paced.py').read_text())
        node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='record_tx')
        responses=iter([None,{'meta':{'err':None}}]);writes=[]
        env={'rpc':lambda *args:next(responses),'URL':'local','time':types.SimpleNamespace(sleep=lambda _:None),'write':lambda *args:writes.append(args)}
        exec(compile(ast.Module(body=[node],type_ignores=[]),'actual-record-tx','exec'),env)
        self.assertEqual(env['record_tx']('public'),{'meta':{'err':None}})
        self.assertEqual(len(writes),1)
        env['rpc']=lambda *args:None
        with self.assertRaisesRegex(RuntimeError,'metadata unavailable'):env['record_tx']('missing')
        self.assertEqual(len(writes),1)
    def actual_wait(self, height):
        tree=ast.parse(pathlib.Path(__file__).with_name('r1_devnet_deploy_paced.py').read_text())
        node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='wait')
        def rpc(url,method,args):
            if method=='getSignatureStatuses':return {'value':[None]}
            if method=='getBlockHeight':return height
            raise AssertionError('must not fetch expired or ambiguous transaction metadata')
        times=iter([0,101])
        env={'rpc':rpc,'URL':'local','time':types.SimpleNamespace(monotonic=lambda:next(times))}
        exec(compile(ast.Module(body=[node],type_ignores=[]),'actual-wait','exec'),env)
        return env['wait']
    def test_expired_unlanded_attempt_allows_refund_reconciliation(self):
        row={'signature':'public','blockhash':{'lastValidBlockHeight':100}}
        self.actual_wait(101)([row],allow_error=True)
        self.assertEqual(row['confirmationStatus'],'expired_unlanded')
    def test_ambiguous_attempt_prevents_refund(self):
        with self.assertRaisesRegex(RuntimeError,'timeout'):
            self.actual_wait(99)([{'signature':'public','blockhash':{'lastValidBlockHeight':100}}],allow_error=True)
    def test_legacy_attempt_without_expiry_is_not_assumed_expired(self):
        with self.assertRaisesRegex(RuntimeError,'timeout'):
            self.actual_wait(1000)([{'signature':'public'}],allow_error=True)
    def test_cpi_creation_included_but_failed_transaction_excluded(self):
        tx={'meta':{'err':None,'preBalances':[100,0],'postBalances':[90,10]},'transaction':{'message':{'accountKeys':['payer','pda']}}}
        self.assertEqual(created_accounts(tx),['pda']);tx['meta']['err']='failure'
        self.assertEqual(created_accounts(tx),[])

if __name__=='__main__':unittest.main()
