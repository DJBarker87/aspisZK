"""Local fixtures and mocks only; never executes a tool, SSH or remote payload."""
import ast
import hashlib
import io
import sys
import importlib.util
import json
import os
from pathlib import Path
import stat
import tempfile
import unittest
from unittest.mock import patch

HERE = Path(__file__).absolute().parent


def load(name):
    spec = importlib.util.spec_from_file_location(name, HERE / (name + '.py'))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


p = load('payload')
t = load('transport')
FIXTURES = Path(tempfile.mkdtemp(prefix='lean-host-probe-20261025-fixtures-', dir='/private/tmp'))


class ProbeTests(unittest.TestCase):
    def setUp(self):
        self.root = FIXTURES / self._testMethodName
        self.root.mkdir(mode=0o700)
        self.file = self.root / 'literal'
        self.file.write_bytes(b'public fixture')

    def observe(self, path=None, role='hash', **kw):
        return p.Probe().observe(str(path or self.file), role, **kw)

    def test_exact_scope(self):
        expected = [p.HOME, p.TOOLCHAINS] + [p.ROOT+'/'+s for s in (
            'bin/lean', 'lib/lean/libleanshared.so', 'lib/lean/libInit_shared.so',
            'lib/lean/libleanshared_1.so', 'lib/lean/libleanshared_2.so',
            'src/lean/Lean/Environment.lean', 'src/lean/Lean/ImportingFlag.lean',
            'src/lean/Lean/Setup.lean', 'src/lean/Lean/CompactedRegion.lean',
            'src/lean/Lean/Compiler/InitAttr.lean', 'lib/lean/Init/Prelude.olean',
            'lib/lean/Init/Prelude.ir', 'lib/lean/Init/Prelude.olean.server',
            'lib/lean/Init/Prelude.olean.private')]
        expected += [p.HOME+'/.elan/bin/lean', p.HISTORICAL+'/run-joint.sh',
                     p.HISTORICAL+'/lean-toolchain', p.SOURCES]
        self.assertEqual([x[0] for x in p.plan()], expected)
        self.assertEqual(len(expected), 20)
        self.assertEqual([x[1] for x in p.plan()].count('names'), 1)
        self.assertEqual([x[2] for x in p.plan()][17:19], [1024*1024]*2)

    def test_hash_and_no_contents(self):
        r = self.observe()
        self.assertEqual(r['sha256'], hashlib.sha256(b'public fixture').hexdigest())
        self.assertNotIn('public fixture', json.dumps(r))
        self.assertTrue(r['ancestors'])
        for a in r['ancestors'] + [r['entry']]:
            self.assertTrue({'uid', 'gid', 'mode', 'nlink', 'group_writable'} <= a.keys())

    def test_names_no_recurse_and_count(self):
        d = self.root / 'names'; d.mkdir()
        (d/'nested').mkdir(); (d/'nested'/'not-visible').write_text('secret fixture')
        (d/'alias').symlink_to('/never-open-this-fixture-target')
        r = self.observe(d, 'names')
        self.assertEqual(r['names'], ['alias', 'nested'])
        for i in range(62): (d/str(i)).touch()
        self.assertEqual(len(self.observe(d, 'names')['names']), 64)
        (d/'65th').touch()
        r = self.observe(d, 'names')
        self.assertEqual(r['outcome'], 'more_than_64_entries')
        self.assertTrue(r['truncated']); self.assertNotIn('names', r)

    def test_name_cap(self):
        class Entry: name = 'x'*257
        class Entries:
            def __enter__(self): return iter([Entry()])
            def __exit__(self, *args): pass
        with patch.object(p.os, 'scandir', return_value=Entries()):
            self.assertEqual(self.observe(self.root, 'names')['outcome'], 'entry_name_over_256')

    def test_alias_and_special_nofollow(self):
        alias = self.root/'alias'; alias.symlink_to(self.file)
        self.assertEqual(self.observe(alias)['outcome'], 'alias_not_followed')
        self.assertEqual(self.observe(alias/'child')['outcome'], 'alias_not_followed')
        self.assertEqual(self.observe(self.file, 'alias_metadata')['outcome'], 'regular_metadata_only')
        fifo = self.root/'fifo'; os.mkfifo(fifo)
        self.assertEqual(self.observe(fifo)['outcome'], 'not_regular')
        real = os.readlink
        with patch.object(p.os, 'readlink', side_effect=lambda *a, **k: 'x'*4097):
            self.assertEqual(self.observe(alias)['outcome'], 'alias_over_4096_bytes')
        self.assertEqual(real(alias), str(self.file))

    def test_caps_and_deadline(self):
        self.assertEqual(self.observe(cap=2)['outcome'], 'file_cap_exceeded')
        probe = p.Probe(); probe.sampled = p.TOTAL_CAP-1
        self.assertEqual(probe.observe(str(self.file), 'hash')['outcome'], 'total_cap_exceeded')
        probe.end = 0
        self.assertEqual(probe.observe(str(self.file), 'hash')['outcome'], 'deadline')
        sizes = []; real = os.read
        with patch.object(p.os, 'read', side_effect=lambda fd, n: (sizes.append(n), real(fd,n))[1]):
            self.observe()
        self.assertLessEqual(max(sizes), 65536)

    def test_drift_invalidates_digest(self):
        real = os.read
        def mutate(fd, n):
            b = real(fd,n)
            self.file.write_bytes(b'changed fixture content')
            return b
        with patch.object(p.os, 'read', side_effect=mutate):
            r = self.observe()
        self.assertEqual(r['outcome'], 'stale_prepost')
        self.assertNotIn('sha256', r)

    def test_stale_open(self):
        real = os.open
        def mutate(name, flags, *a, **kw):
            if name == 'literal': self.file.write_bytes(b'changed')
            return real(name, flags, *a, **kw)
        with patch.object(p.os, 'open', side_effect=mutate):
            self.assertEqual(self.observe()['outcome'], 'stale_prepost')

    def test_fd_closure_readerror_and_missing(self):
        opened, closed = [], []
        real_open, real_close = os.open, os.close
        def opening(*a, **kw):
            fd = real_open(*a, **kw); opened.append(fd); return fd
        def closing(fd): closed.append(fd); return real_close(fd)
        with patch.object(p.os, 'open', side_effect=opening), patch.object(p.os, 'close', side_effect=closing):
            with patch.object(p.os, 'read', side_effect=OSError(5, 'fixture read failure')):
                self.assertEqual(self.observe()['outcome'], 'read_error')
            self.assertEqual(self.observe(self.root/'missing')['outcome'], 'missing')
        self.assertEqual(sorted(opened), sorted(closed))
        self.assertEqual(self.observe(self.root, 'directory')['outcome'], 'directory_metadata_only')

    def test_elf_header(self):
        b = bytearray(64); b[:4] = b'\x7fELF'; b[4:6] = bytes([2,1]); b[18:20] = (62).to_bytes(2,'little')
        self.assertEqual(p.elf_header(b), {'outcome':'header_only','class':2,'data':1,'machine':62})
        b[5] = 2; b[18:20] = (183).to_bytes(2,'big')
        self.assertEqual(p.elf_header(b)['machine'], 183)
        self.assertEqual(p.elf_header(b[:63])['outcome'], 'not_64_byte_ELF_header')

    def test_owner_and_hardlink_data(self):
        os.link(self.file, self.root/'hardlink')
        r = self.observe(); self.assertEqual(r['outcome'], 'hashed'); self.assertEqual(r['entry']['nlink'], 2)
        with patch.object(p.os, 'getuid', return_value=2147483646):
            if os.stat(self.file).st_uid != 0:
                self.assertEqual(self.observe()['outcome'], 'unexpected_owner')

    def test_disabled_mains_and_pins(self):
        self.assertFalse(t.ALLOCATED)
        with patch.object(t.subprocess, 'Popen', side_effect=AssertionError('never launch')):
            with self.assertRaisesRegex(RuntimeError, 'DISABLED'): t.run_once()
        prospective = t.body()
        self.assertEqual(hashlib.sha256(prospective).hexdigest(), t.BODY_SHA)
        self.assertTrue(prospective.endswith((HERE/'footer.py.txt').read_bytes()))
        self.assertNotIn(t.DISABLED_TAIL.encode(), prospective)
        tree = ast.parse((HERE/'payload.py').read_text())
        guard = tree.body[-1]
        self.assertIsInstance(guard.body[0], ast.Raise)
        with patch.object(t, 'PAYLOAD_SHA', '0'*64):
            with self.assertRaisesRegex(RuntimeError, 'source hash'): t.body()

    def test_durable_charge_before_mock_popen(self):
        capture = self.root/'capture'
        events = []; real_fsync = os.fsync
        def sync(fd): events.append('fsync'); real_fsync(fd)
        class MockChild:
            stdin = stdout = stderr = None
            returncode = 0
            def poll(self): return 0
        def mock_popen(argv, **kw):
            self.assertTrue((capture/'charge.json').exists())
            self.assertGreaterEqual(events.count('fsync'), 3)
            charge = json.loads((capture/'charge.json').read_text())
            self.assertEqual(charge['proof_calls'], 0)
            self.assertEqual(tuple(argv), t.ARGV)
            self.assertFalse(kw['shell']); self.assertTrue(kw['close_fds'])
            events.append('mock_popen'); return MockChild()
        def collector(child, data, deadline):
            self.assertEqual(hashlib.sha256(data).hexdigest(), t.BODY_SHA)
            self.assertGreater(deadline, 0)
            return b'{"fixture":true}\n', b''
        with patch.object(t, 'ALLOCATED', True), patch.object(t, 'CAPTURE', str(capture)), patch.object(t.os, 'fsync', side_effect=sync):
            t.run_once(popen=mock_popen, collector=collector)
            with self.assertRaises(FileExistsError): t.run_once(popen=mock_popen, collector=collector)
        self.assertEqual(events.count('mock_popen'), 1)
        self.assertEqual(stat.S_IMODE(capture.stat().st_mode), 0o700)
        self.assertEqual(stat.S_IMODE((capture/'charge.json').stat().st_mode), 0o600)

    def test_payload_main_is_bounded_mock_metadata(self):
        class Sink:
            def __init__(self): self.buffer = io.BytesIO()
        class Uname: machine = 'fixture-machine'; release = 'fixture-release'
        sink = Sink()
        with patch.object(p.Probe, 'observe', return_value={'outcome':'missing'}) as observe, patch.object(p.os, 'uname', return_value=Uname()), patch.object(p.os, 'getuid', return_value=123), patch.object(p.signal, 'signal'), patch.object(p.signal, 'alarm') as alarm, patch.object(p.sys, 'stdout', sink):
            p.main()
            self.assertEqual(observe.call_count, 20)
            self.assertEqual(alarm.call_args_list[0].args, (10,))
            self.assertEqual(alarm.call_args_list[-1].args, (0,))
        report = json.loads(sink.buffer.getvalue())
        self.assertEqual(report['uid'], 123)
        self.assertEqual(report['claim'], 'read_only_metadata_not_admission')
        sink = Sink()
        with patch.object(p.Probe, 'observe', return_value={'oversized_fixture':'x'*60000}), patch.object(p.os, 'uname', return_value=Uname()), patch.object(p.signal, 'signal'), patch.object(p.signal, 'alarm'), patch.object(p.sys, 'stdout', sink):
            p.main()
        self.assertEqual(json.loads(sink.buffer.getvalue())['outcome'], 'output_cap_exceeded')

    def test_mock_launch_failure_is_charged_and_not_retried(self):
        capture = self.root/'failure-capture'
        def fail(*args, **kw):
            self.assertTrue((capture/'charge.json').exists())
            raise OSError('mock launch failed')
        with patch.object(t, 'ALLOCATED', True), patch.object(t, 'CAPTURE', str(capture)):
            with self.assertRaises(OSError): t.run_once(popen=fail)
            self.assertTrue((capture/'failure.json').exists())
            with self.assertRaises(FileExistsError): t.run_once(popen=fail)

    def test_collector_deadline_and_output_cap_mock_only(self):
        class Stream:
            def __init__(self, fd): self.fd = fd
            def fileno(self): return self.fd
            def close(self): pass
        class Child:
            stdin = Stream(101); stdout = Stream(102); stderr = Stream(103)
            def wait(self, timeout): return 0
        class Selector:
            def __init__(self): self.keys = {}
            def __enter__(self): return self
            def __exit__(self, *args): pass
            def register(self, stream, event, tag):
                class Key: pass
                k = Key(); k.fd=stream.fd; k.fileobj=stream; k.data=tag
                self.keys[stream.fd] = k
            def unregister(self, stream): del self.keys[stream.fd]
            def get_map(self): return self.keys
            def select(self, timeout): return [(k, 1) for k in list(self.keys.values())]
        with patch.object(t.selectors, 'DefaultSelector', Selector), patch.object(t.os, 'set_blocking'), patch.object(t.os, 'write', side_effect=lambda fd,b:len(b)), patch.object(t.os, 'read', side_effect=lambda fd,n:b'x'*n):
            with self.assertRaisesRegex(RuntimeError, '1 MiB'): t.collect(Child(), b'fixture', t.time.monotonic()+20)
            with self.assertRaises(TimeoutError): t.collect(Child(), b'fixture', 0)

    def test_source_audit_imports_and_operations(self):
        allow = {'errno','hashlib','json','os','signal','stat','struct','sys','time'}
        tree = ast.parse((HERE/'payload.py').read_text())
        self.assertEqual({n.names[0].name for n in tree.body if isinstance(n, ast.Import)}, allow)
        calls = {n.func.attr for n in ast.walk(tree) if isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute)}
        self.assertFalse(calls & {'system','popen','execve','spawn','setrlimit','unlink','remove','rmdir','listdir','walk','environ'})
        trans = ast.parse((HERE/'transport.py').read_text())
        self.assertEqual(sum(isinstance(n, ast.Call) and isinstance(n.func,ast.Name) and n.func.id=='popen' for n in ast.walk(trans)), 1)
        # Main payload never invokes executable metadata; no version/help/ldd actions.
        self.assertFalse({'subprocess','ctypes','resource','socket'} & allow)


if __name__ == '__main__':
    print('Retained fixture root:', FIXTURES, flush=True)
    result = unittest.main(verbosity=2, exit=False)
    dependencies = {}
    for name, module in sorted(sys.modules.items()):
        path = getattr(module, '__file__', None)
        if isinstance(path, str) and Path(path).is_file() and name != '__main__':
            dependencies[name] = {'path': path, 'sha256': hashlib.sha256(Path(path).read_bytes()).hexdigest()}
    print('Loaded test dependency hashes:', json.dumps(dependencies, sort_keys=True))
    raise SystemExit(not result.result.wasSuccessful())
