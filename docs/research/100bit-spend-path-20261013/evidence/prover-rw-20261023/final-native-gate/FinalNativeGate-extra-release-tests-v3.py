"""Additional exact prospective activation/receipt tests; every action mocked.
No setup/SSH/native call. Kept outside payload to preserve reviewed source bytes.
"""
import ast
import contextlib
import hashlib
import importlib.util
import io
import json
from pathlib import Path
import resource
import sys
import time
from types import SimpleNamespace as NS
import unittest
from unittest.mock import Mock,patch

E=Path(__file__).resolve().parent
D=E.parents[5]/'tools/prover-rw-20261023/final-native-gate'
R=D/'prospective-data-v2'
STAGE=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/final-native-gate')

def pin(raw):return dict(size=len(raw),sha256=hashlib.sha256(raw).hexdigest())

def module(name):
    ns={'__name__':'source_review_only','__file__':str(STAGE/name)}
    with patch.object(Path,'resolve',lambda path:STAGE/name):exec((R/'payload'/name).read_bytes(),ns)
    return ns

class Additional(unittest.TestCase):
    def test_exact_outer_data_main_only_calls_prospective_and_fixed_bootstrap(self):
        ns=module('FinalNativeGate_setup.py');ns['_prospective']=Mock(return_value=17)
        with patch.object(sys,'path',list(sys.path)):
            self.assertEqual(ns['main'](),17);self.assertEqual(sys.path[0],str(STAGE))
        ns['_prospective'].assert_called_once_with()

    def test_wrong_stage_never_calls_prospective(self):
        ns=module('FinalNativeGate_setup.py');ns['HERE']=Path('/synthetic/wrong');ns['_prospective']=Mock()
        with self.assertRaisesRegex(ValueError,'fixed DATA stage'):ns['main']()
        ns['_prospective'].assert_not_called()

    def test_exact_inside_main_only_calls_reviewed_bound_body(self):
        ns=module('FinalNativeGate_setup_inside.py');ns['_bound_body']=Mock(return_value=19)
        self.assertEqual(ns['main'](),19);ns['_bound_body'].assert_called_once_with()

    def test_receiver_main_fixed_data_argv_env_and_failure_receipt(self):
        ns={'__name__':'source_review_only'};exec((R/'FinalNativeGate-data-transfer.py').read_bytes(),ns)
        ns['packet_summary']=Mock(return_value={'synthetic-fixed-terminal':{'record':{'execution_authority':False}}})
        ns['sys']=NS(argv=['fixed-receiver']);ns['install']=Mock(return_value={'status':'FIXED_DATA_SOURCE_TRANSFERRED','execution_authority':False})
        ns['subprocess']=NS(run=Mock(return_value=NS(returncode=78)),DEVNULL='synthetic-devnull')
        with contextlib.redirect_stdout(io.StringIO()) as out:self.assertEqual(ns['main'](),78)
        call=ns['subprocess'].run.call_args
        self.assertEqual(call.args[0],['/usr/bin/python3','-I','-B',str(STAGE/'FinalNativeGate_setup.py')])
        self.assertEqual(call.kwargs['cwd'],str(STAGE));self.assertLessEqual(call.kwargs['timeout'],120)
        self.assertEqual(set(call.kwargs['env']),{'HOME','USER','LOGNAME','PATH','LANG','LC_ALL'})
        value=json.loads(out.getvalue());self.assertEqual(value['setup_exit'],78);self.assertFalse(value['execution_authority'])

    def test_receiver_argument_rejected_before_install(self):
        ns={'__name__':'source_review_only'};exec((R/'FinalNativeGate-data-transfer.py').read_bytes(),ns)
        ns['sys']=NS(argv=['fixed-receiver','not-allowed']);ns['install']=Mock()
        with self.assertRaisesRegex(ValueError,'no receiver arguments'):ns['main']()
        ns['install'].assert_not_called()


def main():
    start=time.monotonic()
    with (E/'FinalNativeGate-extra-release-007.log').open('x') as log:
        result=unittest.TextTestRunner(stream=log,verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Additional))
    u=resource.getrusage(resource.RUSAGE_SELF)
    receipt=dict(argv=[sys.executable,'-B',str(Path(__file__))],exit=0 if result.wasSuccessful() else 1,
        wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss*(1 if sys.platform=='darwin' else 1024),swap=u.ru_nswap,
        source_revision='b34142b016 plus exact source-manifest-007 overlay',source_dependency_manifest=pin((E/'FinalNativeGate-source-manifest-007.json').read_bytes()),
        harness=pin(Path(__file__).read_bytes()),trace_reused=pin((E/'FinalNativeGate-order-traces-006.json').read_bytes()),
        print_axioms='N/A: Python explicit mocks/source bytes; no Lean theorem/import invocation',
        actual_host=0,actual_SSH=0,actual_network=0,actual_metadata=0,actual_setup=0,actual_native=0,actual_compiler=0,
        actual_Rust=0,actual_Cargo=0,actual_Kani=0,actual_Lean=0,actual_extraction=0,actual_backend=0,actual_ELF=0)
    with (E/'FinalNativeGate-extra-release-007.json').open('x') as f:json.dump(receipt,f,sort_keys=True,indent=2)
    print(json.dumps(receipt,sort_keys=True))
    return receipt['exit']

if __name__=='__main__':raise SystemExit(main())
