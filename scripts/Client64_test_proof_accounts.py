"""Offline public-identifier fixtures only: no keygen, secrets, prover or RPC."""
import ast
import copy
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import Client64_proof_accounts as c


def address(i):
    n = int.from_bytes(bytes([i])*32, 'big')
    out = ''
    while n:
        n, r = divmod(n, 58)
        out = c.ALPHABET[r] + out
    return out


class Lifecycle(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)  # public mock files only, never real keys
        self.root = Path(self.temp.name)/'private'
        self.identity = dict(action='prove', pool=address(20), verifier=address(21),
                             checkpoint=address(22), public_account=address(23),
                             verifier_checkpoint=address(24), note=0)
        self.calls = []
        self.generated = []
        self.attempts = 1
        self.failure = None

    def generate(self, path):
        key = address(len(self.generated)+1)
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
        with os.fdopen(fd, 'w') as f:
            f.write(key)  # PUBLIC IDENTIFIER, not a Solana keyfile
        self.generated.append(path)
        return key

    def result(self, q):
        key = q['proof_accounts'][self.attempts-1]
        return dict(client_route=c.ROUTE, attempts=self.attempts,
                    attempt_index=self.attempts-1, proof_account=key,
                    stage1=dict(program=q['verifier'], data='030a', accounts=[
                        [key, False, False], [q['public_account'], False, False],
                        [q['verifier_checkpoint'], False, True]]),
                    settle=dict(program=q['pool'], data='', accounts=[
                        [address(30), False, False], [q['checkpoint'], False, False]] +
                        [[address(31), False, False]]*8 + [[key, False, False],
                        [q['verifier_checkpoint'], False, False]]))

    def invoke(self, q):
        self.calls.append(copy.deepcopy(q))
        if self.failure:
            raise RuntimeError(self.failure)
        directory = Path(q['proof_dir']);directory.mkdir(mode=0o700)
        (directory/'proof.bin').write_bytes(b'public mock proof')
        (directory/'statement.bin').write_bytes(b'public mock statement')
        return self.result(q)

    def run_plan(self, **overrides):
        args = dict(root=self.root, identity=self.identity, prepare=lambda: {'lane_bytes':'00'},
                    invoke=self.invoke, absent=lambda k: True, generate=self.generate,
                    public=lambda p: p.read_text())
        args.update(overrides)
        return c.proof_plan(**args)

    def test_success_first_rejected_then_eighth_and_resume(self):
        for attempts in [1, 2, 8]:
            with self.subTest(attempts=attempts):
                self.root = Path(self.temp.name)/str(attempts);self.generated=[];self.calls=[]
                self.attempts=attempts
                plan, path = self.run_plan()
                self.assertEqual(path, str(self.root/f'attempt-{attempts-1}.json'))
                self.assertEqual(plan['proof_account'], Path(path).read_text())
                self.assertEqual(len(self.generated), 8)
                def forbidden(*_): raise AssertionError('resume must not invoke external work')
                resumed = self.run_plan(invoke=forbidden, prepare=forbidden, generate=forbidden, absent=forbidden)
                self.assertEqual(resumed, (plan, path))
                self.assertEqual(len(self.calls), 1)
                self.assertTrue(all(p.exists() for p in self.generated))
                self.assertEqual(self.root.stat().st_mode & 0o777, 0o700)
                self.assertEqual((self.root/'manifest.json').stat().st_mode & 0o777, 0o600)

    def test_all_reject_fatal_callback_store_error_no_retry(self):
        for failure in ['AttemptsExhausted', 'fatal callback', 'duplicate durable nonce', 'store fsync failure']:
            with self.subTest(failure=failure):
                self.root=Path(self.temp.name)/failure.replace(' ','-');self.generated=[];self.calls=[]
                self.failure=failure
                with self.assertRaisesRegex(RuntimeError, failure): self.run_plan()
                with self.assertRaisesRegex(ValueError, 'incomplete'): self.run_plan()
                self.assertEqual(len(self.calls), 1)
                self.assertEqual(len(self.generated), 8)
                self.assertTrue(all(p.exists() for p in self.generated))

    def test_malformed_missing_zero_duplicate_lists(self):
        keys = [address(i) for i in range(1, 9)]
        for bad in [None, [], keys[:-1], keys+[address(9)], ['bad']+keys[1:],
                    ['1'*32]+keys[1:], [False]+keys[1:], keys[:-1]+[keys[0]]]:
            with self.subTest(bad=bad), self.assertRaises(ValueError): c.validate_keys(bad)

    def test_bad_key_generation_is_retained_and_not_retried(self):
        with self.assertRaisesRegex(ValueError, 'duplicate'):
            self.run_plan(generate=lambda path: address(1))
        with self.assertRaisesRegex(ValueError, 'incomplete'): self.run_plan()
        self.assertEqual(self.calls, [])

    def test_wrong_mapping_is_not_published(self):
        def wrong(q):
            result=self.invoke(q);result['proof_account']=address(8);return result
        with self.assertRaisesRegex(ValueError, 'mismatch'): self.run_plan(invoke=wrong)
        with self.assertRaisesRegex(ValueError, 'incomplete'): self.run_plan()
        self.assertEqual(len(self.generated), 8)

    def test_all_instruction_roles_checked(self):
        keys=[address(i) for i in range(1,9)];q={**self.identity,'proof_accounts':keys}
        valid=self.result(q)
        for field,index in [('stage1',0),('stage1',1),('stage1',2),('settle',10),('settle',-1),('settle',1)]:
            plan=copy.deepcopy(valid);plan[field]['accounts'][index][0]=address(40)
            with self.subTest(field=field,index=index), self.assertRaises(ValueError):
                c.validate_plan(plan,keys,self.identity)
        for changes in [dict(attempts=0),dict(attempts=9),dict(attempt_index=1),
                        dict(attempts=True),dict(attempt_index=False),dict(client_route='generic96')]:
            with self.assertRaises(ValueError): c.validate_plan({**valid,**changes},keys,self.identity)

    def test_funded_account_refused(self):
        with self.assertRaisesRegex(ValueError, 'already exists'): self.run_plan(absent=lambda _:False)
        self.assertEqual(self.calls, [])
        with self.assertRaisesRegex(ValueError, 'incomplete'): self.run_plan()

    def test_failure_persisting_entered_never_invokes_or_regenerates(self):
        real=c.atomic_json
        def fail(path,state):
            if state['state']=='entered': raise OSError('disk failure')
            real(path,state)
        with patch.object(c,'atomic_json',fail), self.assertRaisesRegex(OSError,'disk failure'):
            self.run_plan()
        with self.assertRaisesRegex(ValueError,'incomplete'): self.run_plan()
        self.assertEqual(self.calls,[]);self.assertEqual(len(self.generated),8)

    def test_ambiguous_claim_blocks_without_reset(self):
        self.failure='crash'
        with self.assertRaises(RuntimeError): self.run_plan()
        state=json.loads((self.root/'manifest.json').read_text());state['state']='ready'
        c.atomic_json(self.root/'manifest.json',state)
        with self.assertRaises(FileExistsError): self.run_plan()
        self.assertEqual(len(self.calls),1)

    def test_resume_checks_identity_paths_public_artifact_and_export(self):
        plan,_=self.run_plan();manifest=self.root/'manifest.json';original=manifest.read_text()
        bad=json.loads(original);bad['keys'][0]['path']='/unrelated'
        c.atomic_json(manifest,bad)
        with self.assertRaisesRegex(ValueError,'mapping changed'):self.run_plan()
        manifest.write_text(original)
        with self.assertRaisesRegex(ValueError,'mapping changed'): self.run_plan(public=lambda _:address(50))
        with self.assertRaisesRegex(ValueError,'incomplete'): self.run_plan(identity={**self.identity,'note':1})
        export=Path(self.temp.name)/'export.json';export.write_text('{}')
        with self.assertRaisesRegex(ValueError,'differs'):self.run_plan(legacy_plan=export)
        export.write_text(json.dumps(plan));self.run_plan(legacy_plan=export)
        (self.root/'proof'/'proof.bin').write_bytes(b'changed')
        with self.assertRaisesRegex(ValueError,'artifacts changed'):self.run_plan()

    def test_missing_and_legacy_mapping_and_partial_allocation(self):
        legacy=Path(self.temp.name)/'legacy.json';legacy.write_text('{}')
        with self.assertRaisesRegex(ValueError,'legacy'):self.run_plan(legacy_plan=legacy)
        self.assertFalse(self.root.exists())
        self.root.mkdir(mode=0o700)
        with self.assertRaises(FileNotFoundError):self.run_plan()
        c.atomic_json(self.root/'manifest.json',dict(state='allocating',identity=self.identity))
        with self.assertRaisesRegex(ValueError,'incomplete'):self.run_plan()
        self.assertEqual(self.generated,[])

    def test_actual_key_retention_publication_uses_durable_private_files(self):
        self.root.mkdir(mode=0o700)
        path=self.root/'attempt-0.json';seen=[]
        def generate_command(command,**kwargs):
            stage=Path(command[-1])
            self.assertFalse(path.exists())
            stage.write_text(address(1))  # public mock identifier only
        def pubkey_command(command,**kwargs):
            retained=Path(command[-1]);seen.append(retained)
            self.assertEqual(retained,path)
            self.assertTrue(path.with_name(path.name+'.generated-private').exists())
            self.assertEqual(retained.stat().st_mode & 0o777,0o600)
            return address(1)+'\n'
        with patch.object(c.subprocess,'run',generate_command), patch.object(c.subprocess,'check_output',pubkey_command):
            self.assertEqual(c.retain_key(path,Path('/mock')),address(1))
            with self.assertRaisesRegex(ValueError,'already exists'):c.retain_key(path,Path('/mock'))
        self.assertEqual(path.read_text(),address(1));self.assertEqual(len(seen),1)

    def test_success_persistence_failure_is_not_reproved(self):
        real=c.atomic_json
        def fail(path,state):
            if state['state']=='success':raise OSError('success write failure')
            real(path,state)
        with patch.object(c,'atomic_json',fail),self.assertRaisesRegex(OSError,'success write failure'):
            self.run_plan()
        with self.assertRaisesRegex(ValueError,'incomplete'):self.run_plan()
        self.assertEqual(len(self.calls),1);self.assertEqual(len(self.generated),8)
        self.assertTrue((self.root/'proof'/'proof.bin').exists())

    def test_resume_request_mapping_and_permissions(self):
        self.run_plan();manifest=self.root/'manifest.json';original=manifest.read_text()
        state=json.loads(original);state['request']['proof_accounts'].reverse()
        c.atomic_json(manifest,state)
        with self.assertRaisesRegex(ValueError,'request mapping changed'):self.run_plan()
        manifest.write_text(original);os.chmod(manifest,0o644)
        with self.assertRaisesRegex(ValueError,'0600'):self.run_plan()

    def test_actual_script_refuses_missing_retained_auxiliary_key(self):
        source=Path(__file__).with_name('r1_devnet_spend.py').read_text()
        tree=ast.parse(source)
        node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='key')
        env=dict(C={},re=__import__('re'),pathlib=__import__('pathlib'),os=os,subprocess=c.subprocess)
        exec(compile(ast.fix_missing_locations(ast.Module(body=[node],type_ignores=[])),'actual-key-helper','exec'),env)
        with patch.object(c.subprocess,'run',side_effect=AssertionError('must not generate')):
            with self.assertRaisesRegex(RuntimeError,'missing retained key'):
                env['key']('Client64-public-mock-missing',require_existing=True)

    def test_actual_script_selected_key_create_upload_settlement_wiring(self):
        # Execute the actual script's spend preparation/publication statements,
        # with only external effects mocked. No copy of its selection logic.
        source=Path(__file__).with_name('r1_devnet_spend.py').read_text()
        tree=ast.parse(source)
        loop=next(node for node in tree.body if isinstance(node,ast.For) and
                  isinstance(node.target,ast.Tuple) and [x.id for x in node.target.elts if isinstance(x,ast.Name)] == ['n','label'])
        end=next(i for i,node in enumerate(loop.body) if isinstance(node,ast.Assign) and
                 any(isinstance(x,ast.Name) and x.id=='readback' for x in node.targets))
        code=compile(ast.fix_missing_locations(ast.Module(body=loop.body[:end],type_ignores=[])),'actual-spend-loop','exec')
        self.root=Path(self.temp.name)/'transfer-client64-proof-private';self.attempts=2
        sent=[];created=[];uploaded=[];writes={}
        programs=dict(pool=address(20),verifier=address(21))
        env=dict(O=Path(self.temp.name),C=dict(programs=programs,payer=address(25),carrier=address(26)),
                 CLI=Path('/mock'),n=0,label='transfer',mint=address(27),dest=address(28),
                 cp=dict(checkpoint=address(22)),deposits=[dict(output_lane=address(29))],
                 key=lambda name,**kwargs:(f'/retained/{name}',address(23 if name.endswith('public') else 24)),
                 proof_plan=c.proof_plan,retain_key=lambda path,cli:self.generate(path),
                 key_public=lambda path,cli:path.read_text(),readhex=lambda *_:'00',
                 invoke=self.invoke,account=lambda _:dict(value=None),
                 write=lambda name,value:writes.update({name:value}),
                 create=lambda *args:created.append(args),
                 upload=lambda label,account,path,body:uploaded.append((account,path)) or dict(
                     count=16 if 'proof-upload' in label else 1,wall_seconds=0,wall_origin_kind='mock',compute_units=0),
                 send=lambda name,instructions:sent.append((name,instructions)),time=__import__('time'))
        exec(code,env)
        selected=address(2);path=str(self.root/'attempt-1.json')
        self.assertEqual(created[0][1],selected);self.assertEqual(created[0][-1],path)
        self.assertEqual(uploaded[0],(selected,path))
        self.assertEqual(sent[0][1][0]['accounts'][0][0],selected)
        self.assertEqual(sent[1][1][0]['accounts'][10][0],selected)
        self.assertEqual(writes['transfer-proof-plan']['attempt_index'],1)
        exec(code,env)  # actual script resumes from private success
        self.assertEqual(len(self.calls),1)


if __name__ == '__main__':
    unittest.main()
