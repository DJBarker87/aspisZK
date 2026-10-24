"""Focused v2 env/argv/epoch checks only; historical groups are REUSED."""
import ast
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
import unittest
from unittest.mock import patch
import ResourceAdmit_host as h
import ResourceAdmit_local as local
import ResourceAdmit_adapter as a

class ResourceAdmitV2Tests(unittest.TestCase):
    def test_literal_inner_env_and_argv(self):
        env=local.env(1000);argv=h.scope_argv(dict(env=env))
        self.assertEqual(argv[:14],['/usr/bin/systemd-run','--user','--scope','--unit='+h.UNIT,
            '-p','MemoryHigh=3G','-p','MemoryMax=4G','-p','MemorySwapMax=0','-p','TasksMax=64','/usr/bin/env','-i'])
        self.assertEqual(argv[14:21],[k+'='+v for k,v in sorted(env.items())])
        self.assertEqual(argv[21:],['/usr/bin/python3','-I','-B',h.STAGE+'/ResourceAdmit_host.py','go'])
        self.assertEqual(shlex.split(shlex.join(argv)),argv)
        self.assertEqual(a.UNIT,h.UNIT)
        for p in Path(__file__).parent.glob('ResourceAdmit_*.py'):ast.parse(p.read_text())

    def test_injected_keys_and_value_drift_still_deny(self):
        expected=local.env(1000)
        with patch.dict(os.environ,expected,clear=True):h.verify_environment(expected)
        for key in ('INVOCATION_ID','JOURNAL_STREAM','SYSTEMD_EXEC_PID','UNKNOWN_KEY'):
            dirty=dict(expected,**{key:'synthetic-sensitive-value'})
            with patch.dict(os.environ,dirty,clear=True),self.assertRaises(ValueError) as error:
                h.verify_environment(expected)
            text=str(error.exception);self.assertIn(key,text);self.assertNotIn('synthetic-sensitive-value',text)
            diagnostic=json.loads(text.split(': ',1)[1]);self.assertEqual(diagnostic['unexpected_keys'],[key])
        dirty=dict(expected,LANG='synthetic-value-drift')
        with patch.dict(os.environ,dirty,clear=True),self.assertRaises(ValueError) as error:h.verify_environment(expected)
        self.assertNotIn('synthetic-value-drift',str(error.exception))
        del dirty['HOME']
        with patch.dict(os.environ,dirty,clear=True),self.assertRaisesRegex(ValueError,'HOME'):h.verify_environment(expected)

    def test_real_env_reconstructs_exact_map_without_shell(self):
        expected=local.env(1000)
        dirty=dict(expected,INVOCATION_ID='injected',JOURNAL_STREAM='1:2',SYSTEMD_EXEC_PID='42',UNKNOWN_KEY='unknown')
        dirty['LANG']='value drift'
        inner=h.scope_argv(dict(env=expected))[12:21]
        # Inspect env's direct output: local macOS Python adds a CF key itself.
        # Target Linux Python is still subject to unchanged exact verify().
        command=inner+['/usr/bin/env']
        result=subprocess.run(command,env=dirty,text=True,capture_output=True,check=True)
        observed=dict(line.split('=',1) for line in result.stdout.splitlines())
        self.assertEqual(observed,expected)
        with patch.dict(os.environ,observed,clear=True):h.verify_environment(expected)
        with patch.dict(os.environ,dirty,clear=True),self.assertRaises(ValueError):h.verify_environment(expected)
        tricky=dict(expected,HOME="quote'\n$()` value")
        argv=h.scope_argv(dict(env=tricky));self.assertEqual(shlex.split(shlex.join(argv)),argv)
        result=subprocess.run(argv[12:21]+['/usr/bin/env'],env=dirty,text=True,capture_output=True,check=True)
        self.assertEqual(result.stdout,''.join(k+'='+v+'\n' for k,v in sorted(tricky.items())))

    def test_epoch_stage_binding_and_unchanged_policy(self):
        self.assertEqual(local.REMOTE,h.STAGE)
        self.assertEqual(local.OUT,local.ROOT/'evidence/resource-admit-20261024/v2')
        self.assertEqual(h.EPOCH,'ResourceAdmit-20261025-v2')
        self.assertEqual(local.coordination()['epochs_total'],2)
        manifest=dict(epoch=h.EPOCH,stage=h.STAGE,env=local.env(1000))
        manifest['scope_argv']=h.scope_argv(manifest)
        with patch.object(h,'HERE',Path(h.STAGE)):
            for key,value in [('epoch','old'),('stage','/old')]:
                with self.assertRaisesRegex(ValueError,'epoch/stage'):h.verify(dict(manifest,**{key:value}))
            with self.assertRaisesRegex(ValueError,'literal scope argv'):h.verify(dict(manifest,scope_argv=[]))
        self.assertEqual(a.EXPECTED,h.EXPECTED)
        with self.assertRaises(RuntimeError):a.go['read_only_admission'](phase='prospective',additional_bytes=4*a.c.GIB)
        denied={'decision':{'allowed':False}}
        self.assertFalse(h.flow(lambda:denied,lambda:self.fail('scope'))['scope_created'])
        self.assertIsNone(h.go_flow(denied,lambda:self.fail('marker'))['marker_exit'])

    def test_v2_once_before_transport_old_sentinel_retained(self):
        with tempfile.TemporaryDirectory() as t:
            root=Path(t);old=root/'ATTEMPTED';old.write_text('old retained')
            new=root/'v2';new.mkdir();(new/'manifest.json').write_text(json.dumps(dict(env=local.env(1000))))
            with patch.object(local,'OUT',new),patch.object(local,'revision',return_value='test-source'),patch.object(subprocess,'run',side_effect=subprocess.TimeoutExpired(['ssh'],120,output=b'retained failure')):
                with self.assertRaises(subprocess.TimeoutExpired):local.run()
                self.assertTrue((new/'ATTEMPTED').exists());self.assertTrue((new/'run-transport.json').exists())
                with self.assertRaises(FileExistsError):local.run()
            self.assertEqual(old.read_text(),'old retained')

if __name__=='__main__':unittest.main(verbosity=2)
