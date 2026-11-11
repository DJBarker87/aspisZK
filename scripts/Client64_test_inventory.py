"""Offline public-only fixtures exercising discovery and actual report entrypoint."""
import base64
import contextlib
import hashlib
import io
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import Client64_inventory as inv
import r1_devnet_inventory as entry
import Client64_test_proof_accounts as lifecycle
address = lifecycle.address


class Inventory(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(); self.addCleanup(self.tmp.cleanup)
        self.old = Path.cwd(); os.chdir(self.tmp.name); self.addCleanup(os.chdir, self.old)
        for name in ('keys','artifacts','receipts/spend','receipts/deploy-fresh'):
            Path(name).mkdir(parents=True, exist_ok=True)
        self.config = dict(payer=address(90), rpc_url='offline stub only', release_artifacts={})
        self.calls=[]
        self.put('keys/payer.json', address(90))
        self.put('artifacts/old-keypair.json', address(91))
        self.make_run(Path('receipts/spend'))
        for i, role in enumerate(('verifier','pool','registry','carrier')):
            self.put(f'receipts/deploy-fresh/{role}-programdata.json', {'address':address(100+i)})
            self.config['release_artifacts']['devnet_verifier' if role=='verifier' else role]={'sha256':hashlib.sha256(b'elf').hexdigest()}

    def put(self, path, data, mode=0o600):
        p=Path(path); p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(data if isinstance(data,str) else json.dumps(data)); p.chmod(mode)
        return p

    def make_run(self, root, recovery=True):
        root.mkdir(parents=True,exist_ok=True)
        self.put(root/'setup-plan.json', dict(vault=address(110),vault_authority=address(111),
            master=address(112),registry_account=address(113),entry=address(114),lanes=[address(115)]))
        for op in ('transfer','withdrawal'):
            f=lifecycle.Lifecycle(); f.setUp(); self.addCleanup(f.doCleanups)
            f.root=(root/f'{op}-client64-proof-private').absolute(); f.attempts=2
            plan,_=f.run_plan()
            # Planner fixture emits public bytes only. Real planner uses these modes.
            (f.root/'proof').chmod(0o700)
            # Actual durable store uses create_dir_all with process umask.
            (f.root/'proof/mask-nonce-ledger').mkdir(mode=0o755)
            self.put(f.root/'proof/mask-nonce-ledger/public-fixture.burn','public fixture')
            for p in (f.root/'proof').iterdir():
                if p.is_file(): p.chmod(0o644)
            if recovery: self.put(f.root/'proof/note-recovery.json', {'public_fixture':True})
            state=json.loads((f.root/'manifest.json').read_text())
            state['plan']['marker']=address(116)
            self.put(f.root/'manifest.json',state)
            self.put(root/f'{op}-proof-plan.json',state['plan'])
            for p in f.generated:
                os.link(p, str(p)+'.generated-private')

    def rpc(self, url, method, params):
        self.assertEqual(url,'offline stub only'); self.calls.append((method,params))
        if method=='getMultipleAccounts':
            self.assertLessEqual(len(params[0]),100)
            token=bytes([1])*32+bytes([2])*32+(42).to_bytes(8,'little')+bytes(93)
            def account(k):
                return dict(lamports=123,owner='TokenkegQfeZyiNwAJbNbGKPFXCWuBvf9Ss623VQ5DA',executable=False,data=[base64.b64encode(token).decode(),'base64'])
            return dict(context={'slot':7},value=[account(k) for k in params[0]])
        self.assertEqual(method,'getAccountInfo')
        role=('verifier','pool','registry','carrier')[[address(100+i) for i in range(4)].index(params[0])]
        data=(3).to_bytes(4,'little')+bytes(8)+bytes([role in ('pool','carrier')])+bytes([90])*32+b'elf'
        return dict(context={'slot':8},value=dict(lamports=55,owner='BPFLoaderUpgradeab1e11111111111111111111111',executable=False,data=[base64.b64encode(data).decode(),'base64']))

    def report(self):
        return inv.build_report(self.config,lambda p:p.read_text(),self.rpc)

    def test_actual_entrypoint_selected_after_rejection_and_legacy_coexist(self):
        self.put('keys/legacy-proof.json',address(92))
        p=Path('receipts/spend/transfer-proof-private'); p.mkdir(mode=0o700)
        self.put(p/'note-recovery.json',{'public_legacy_fixture':True})
        self.put('config.json',self.config)
        with contextlib.redirect_stdout(io.StringIO()):
            status=entry.main(['config.json','public-report.json'],lambda p:p.read_text(),self.rpc)
        self.assertEqual(status,0)
        r=json.loads(Path('public-report.json').read_text())
        self.assertTrue(r['complete']); self.assertEqual(len(r['note_recovery_files']),3)
        self.assertEqual(len(r['keys']),35)  # 32 selected paths plus three legacy/artifact
        for op in ('transfer','withdrawal'):
            paths={Path(k['path']).name:k for k in r['keys'] if f'{op}-client64' in k['path']}
            self.assertEqual(len(paths),16)
            self.assertEqual(paths['attempt-1.json']['pubkey'],address(2))
            self.assertTrue(all(k['mode']=='0o600' for k in paths.values()))
        queried=[k for method,p in self.calls if method=='getMultipleAccounts' for k in p[0]]
        self.assertEqual(len(queried),len(set(queried)))
        self.assertEqual(r['accounts'][address(2)]['lamports'],123)
        self.assertEqual(r['accounts'][address(110)]['token']['amount_base_units'],42)
        self.assertEqual(r['programs']['pool']['upgrade_authority'],address(90))
        self.assertNotIn('public_fixture',Path('public-report.json').read_text())

    def test_repeat_custom_roots_dedup_and_batches_over_100(self):
        self.make_run(Path('receipts/spend-repeat-2'))
        self.make_run(Path('custom/run'))
        self.config['inventory_spend_roots']=['custom/run']
        self.config['inventory_key_roots']=['custom/keys']
        Path('custom/keys').mkdir()
        for i in range(120): self.put(f'custom/keys/{i}.json',address(i+1))
        r=self.report(); self.assertTrue(r['complete'],r['errors'])
        self.assertEqual(len(r['keys']),218)
        batches=[p[0] for m,p in self.calls if m=='getMultipleAccounts']
        self.assertEqual(len(batches),2); self.assertEqual(len(batches[0]),100)
        self.assertEqual(len(sum(batches,[])),len(set(sum(batches,[]))))
        self.assertEqual(len(r['note_recovery_files']),6)

    def test_partial_allocation_and_staging_remain_visible_no_rpc(self):
        private=Path('receipts/spend/partial-client64-proof-private'); private.mkdir(mode=0o700)
        self.put(private/'manifest.json',{'state':'allocating','identity':{}})
        self.put(private/'attempt-0.json.generated-private',address(80))
        self.put(private/'manifest.json.staging-1',{'state':'allocating'})
        r=self.report(); self.assertFalse(r['complete']); self.assertTrue(r['errors']); self.assertEqual(self.calls,[])
        self.assertIn(address(80),[k['pubkey'] for k in r['keys']])
        self.assertTrue((private/'attempt-0.json.generated-private').exists())

    def test_failed_fatal_and_entered_keep_all_attempts(self):
        for state in ('failed','entered','ready'):
            with self.subTest(state=state):
                p=Path('receipts/spend/transfer-client64-proof-private/manifest.json')
                data=json.loads(p.read_text());data['state']=state;self.put(p,data)
                r=self.report(); self.assertFalse(r['complete']);self.assertEqual(len(r['keys']),34)
                self.assertEqual(self.calls,[])

    def test_missing_mapping_file_fails_closed_preserves_staging(self):
        # Public fixture only: simulate interrupted allocation, without deleting files.
        p=Path('receipts/spend/transfer-client64-proof-private/manifest.json')
        data=json.loads(p.read_text()); data['keys'][0]['path']=str(p.parent/'missing.json');self.put(p,data)
        r=self.report(); self.assertFalse(r['complete']);self.assertEqual(len(r['keys']),34)
        self.assertEqual(self.calls,[])

    def test_missing_actual_mapped_file(self):
        private=Path('receipts/spend/missing-client64-proof-private'); private.mkdir(mode=0o700)
        entries=[dict(path=str((private/f'attempt-{i}.json').absolute()),public=address(i+1)) for i in range(8)]
        self.put(private/'manifest.json',dict(state='ready',keys=entries))
        self.put(private/'attempt-0.json.generated-private',address(1))
        r=self.report();self.assertFalse(r['complete']);self.assertEqual(self.calls,[])
        self.assertEqual(len(r['keys']),35)

    def test_mode_unreadable_symlink_and_malformed_private_fail_closed(self):
        p=Path('receipts/spend/transfer-client64-proof-private/attempt-0.json')
        for mode in (0o644,0o000):
            with self.subTest(mode=mode):
                p.chmod(mode);r=self.report();self.assertFalse(r['complete']);self.assertEqual(self.calls,[])
        p.chmod(0o600)
        self.put('receipts/spend/transfer-client64-proof-private/manifest.json','not JSON SECRET SENTINEL')
        r=self.report();self.assertFalse(r['complete']);self.assertNotIn('SECRET SENTINEL',json.dumps(r))
        Path('keys/symlink.json').symlink_to(Path('payer.json'))
        r=self.report();self.assertFalse(r['complete']);self.assertEqual(self.calls,[])

    def test_missing_nested_recovery_and_legacy_flat_required(self):
        private=Path('receipts/spend/old-proof-private'); private.mkdir(mode=0o700)
        self.put('receipts/spend/old-proof-plan.json',{'marker':address(117)})
        # Known transfer legacy plan requires its exact flat file even if others exist.
        self.put('receipts/spend/transfer-proof-plan.json',{'marker':address(117)})
        r=self.report();self.assertFalse(r['complete']);self.assertEqual(self.calls,[])

    def test_missing_nested_recovery_in_success_manifest(self):
        self.make_run(Path('receipts/spend-no-recovery'), recovery=False)
        r=self.report();self.assertFalse(r['complete']);self.assertEqual(self.calls,[])
        self.assertEqual(len(r['keys']),66)

    def test_incomplete_entrypoint_outputs_public_error_and_nonzero(self):
        self.put('receipts/spend/transfer-client64-proof-private/manifest.json', {'state':'allocating'})
        self.put('config.json',self.config)
        with contextlib.redirect_stdout(io.StringIO()):
            code=entry.main(['config.json','incomplete-report.json'],lambda p:p.read_text(),self.rpc)
        self.assertEqual(code,1); self.assertEqual(self.calls,[])
        r=json.loads(Path('incomplete-report.json').read_text())
        self.assertFalse(r['complete']);self.assertEqual(len(r['keys']),34)
        self.assertEqual(r['accounts'],{});self.assertTrue(r['errors'])

    def test_private_directory_modes_and_ancestor_symlink(self):
        p=Path('receipts/spend/transfer-client64-proof-private/proof')
        p.chmod(0o755)
        r=self.report();self.assertFalse(r['complete']);self.assertEqual(self.calls,[])
        p.chmod(0o700)
        Path('alias').symlink_to(Path('receipts/spend').absolute(),target_is_directory=True)
        self.config['inventory_spend_roots']=['alias']
        r=self.report();self.assertFalse(r['complete']);self.assertEqual(self.calls,[])

    def test_mapped_public_mismatch_and_export_mismatch(self):
        p=Path('receipts/spend/transfer-client64-proof-private/manifest.json')
        data=json.loads(p.read_text());data['keys'][0]['public']=address(88);self.put(p,data)
        r=self.report();self.assertFalse(r['complete']);self.assertEqual(self.calls,[])
        data['keys'][0]['public']=address(1);self.put(p,data)
        self.put('receipts/spend/transfer-proof-plan.json',{'marker':address(117),'client_route':'selected64-proof-account-v1'})
        r=self.report();self.assertFalse(r['complete']);self.assertEqual(self.calls,[])

    def test_keytool_failure_never_prints_output_or_mutates_mode(self):

        def bad(_): raise RuntimeError('SECRET SENTINEL')
        r,_,_=inv.discover(self.config,bad)
        self.assertTrue(r['errors']);self.assertNotIn('SECRET SENTINEL',json.dumps(r))
        self.assertEqual(Path('keys/payer.json').stat().st_mode & 0o777,0o600)

    def assert_listing_failure_report(self, failed, exception):
        original = os.scandir
        failed = failed.absolute()
        def scandir(path):
            if Path(path).absolute() == failed:
                raise exception('PRIVATE ERROR SENTINEL')
            return original(path)
        self.put('config.json', self.config)
        output = f'listing-{len(list(Path(".").glob("listing-*.json")))}.json'
        with patch.object(os, 'scandir', scandir), contextlib.redirect_stdout(io.StringIO()):
            code = entry.main(['config.json', output], lambda p:p.read_text(), self.rpc)
        r = json.loads(Path(output).read_text())
        self.assertEqual(code, 1)
        self.assertFalse(r['complete']); self.assertTrue(r['errors'])
        self.assertEqual(self.calls, []); self.assertEqual(r['accounts'], {})
        self.assertIn(address(90), [k['pubkey'] for k in r['keys']])
        self.assertNotIn('PRIVATE ERROR SENTINEL', json.dumps(r))
        return r

    def test_nested_scandir_failure_actual_report(self):
        for root in ('keys', 'artifacts', 'receipts/spend'):
            nested = Path(root)/'nested'; nested.mkdir()
            retained = self.put(nested/'hidden-keypair.json', address(81))
            for exception in (PermissionError, OSError):
                with self.subTest(root=root, exception=exception.__name__):
                    r = self.assert_listing_failure_report(nested, exception)
                    self.assertIn(address(91), [k['pubkey'] for k in r['keys']])
                    if root == 'receipts/spend':
                        self.assertTrue({address(i) for i in range(1, 9)} <=
                                        {k['pubkey'] for k in r['keys']})
                    self.assertTrue(retained.exists())

    def test_repeat_root_scandir_failure_actual_report(self):
        self.make_run(Path('receipts/spend-repeat-2'))
        for exception in (PermissionError, OSError):
            with self.subTest(exception=exception.__name__):
                r = self.assert_listing_failure_report(Path('receipts'), exception)
                self.assertEqual(len(r['keys']), 34)
                self.assertTrue(any(e['path'] == 'receipts' for e in r['errors']))


if __name__=='__main__': unittest.main()
