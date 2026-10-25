"""New finite source/data fixtures only; all acquisition FS APIs are synthetic."""
import ast
import copy
import hashlib
import json
import os
from pathlib import Path
import stat
from types import SimpleNamespace
import unittest
import SbfRuntimeFinish_core as core

HERE = Path(__file__).resolve().parent
OUT = HERE.parents[1] / 'evidence/sbf-runtime-finish-20261025'
PLAN = json.loads((OUT / 'SbfRuntimeFinish-plan.json').read_text())


class FS:
    def __init__(self):
        self.nodes, self.fds, self.nextfd = {}, {}, 4
        self.add('/', stat.S_IFDIR | 0o755)
        self.onread = None
        self.onopen = None

    def add(self, path, mode=stat.S_IFREG | 0o644, data=b'config', target=None, **kw):
        if path != '/':
            parent = path.rsplit('/', 1)[0] or '/'
            if parent not in self.nodes:
                self.add(parent, stat.S_IFDIR | 0o755)
        node = dict(st_dev=1, st_ino=len(self.nodes)+1, st_mode=mode, st_uid=0, st_gid=0,
                    st_nlink=1, st_size=len(target if target is not None else data),
                    st_mtime_ns=123000000000, st_ctime_ns=123000000000,
                    data=data, target=target)
        node.update(kw)
        self.nodes[path] = node
        return node

    def resolve(self, name, dir_fd=None):
        return name if name.startswith('/') else self.fds[dir_fd][0].rstrip('/') + '/' + name

    def stat(self, name, dir_fd=None, follow_symlinks=False):
        assert follow_symlinks is False
        path = self.resolve(name, dir_fd)
        if path not in self.nodes:
            raise FileNotFoundError(path)
        return SimpleNamespace(**self.nodes[path])

    def open(self, name, flags, dir_fd=None):
        assert flags & os.O_NOFOLLOW and flags & os.O_CLOEXEC
        path = self.resolve(name, dir_fd)
        if self.onopen:
            self.onopen(path)
        node = self.nodes[path]
        if stat.S_ISLNK(node['st_mode']):
            raise OSError('nofollow')
        if flags & os.O_DIRECTORY:
            assert stat.S_ISDIR(node['st_mode'])
        fd = self.nextfd
        self.nextfd += 1
        self.fds[fd] = [path, node, 0]
        return fd

    def fstat(self, fd):
        return SimpleNamespace(**self.fds[fd][1])

    def readlink(self, name, dir_fd=None):
        return self.nodes[self.resolve(name, dir_fd)]['target']

    def read(self, fd, n):
        path, node, offset = self.fds[fd]
        if self.onread:
            self.onread(path)
        data = node['data'][offset:offset+n]
        self.fds[fd][2] += len(data)
        return data

    def close(self, fd):
        del self.fds[fd]


def ssl():
    fs = FS()
    fs.add('/etc/ssl/openssl.cnf')
    fs.add('/usr/lib/ssl/openssl.cnf', stat.S_IFLNK | 0o777, target='/etc/ssl/openssl.cnf')
    return fs


def run(fs, path='/usr/lib/ssl/openssl.cnf', **kw):
    attempts = []
    raw, row = core.acquire(path, attempts, fs, **kw)
    assert attempts == [row] and not fs.fds
    return raw, row


class Suite(unittest.TestCase):
    def test_ssl_usr_spelling_complete_chain(self):
        raw, row = run(ssl())
        self.assertEqual((raw, row['physical'], row['status']), (b'config', '/etc/ssl/openssl.cnf', 'PINNED'))
        self.assertIn('/etc/ssl', [c['path'] for c in row['chain']])
        self.assertEqual(len(row['symlinks']), 1)

    def test_ssl_etc_spelling_direct(self):
        self.assertEqual(run(ssl(), '/etc/ssl/openssl.cnf')[1]['status'], 'PINNED')

    def test_ssl_etc_to_usr_reverse_alias(self):
        fs = FS()
        fs.add('/usr/lib/ssl/openssl.cnf')
        fs.add('/etc/ssl/openssl.cnf', stat.S_IFLNK | 0o777, target='/usr/lib/ssl/openssl.cnf')
        self.assertEqual(run(fs, '/etc/ssl/openssl.cnf')[1]['status'], 'PINNED')

    def test_ssl_relative_exact_target(self):
        fs = ssl()
        fs.nodes['/usr/lib/ssl/openssl.cnf']['target'] = '../../../etc/ssl/openssl.cnf'
        self.assertEqual(run(fs)[1]['status'], 'PINNED')

    def test_ssl_reject_other_etc_ssl_endpoint(self):
        fs = ssl()
        fs.nodes['/usr/lib/ssl/openssl.cnf']['target'] = '/etc/ssl/private.cnf'
        self.assertEqual(run(fs)[1]['status'], 'ERROR')

    def test_ssl_reject_public_detour(self):
        fs = ssl()
        fs.nodes['/usr/lib/ssl/openssl.cnf']['target'] = '/usr/lib/other.cnf'
        self.assertEqual(run(fs)[1]['status'], 'ERROR')

    def test_ssl_reject_etc_escape(self):
        fs = ssl()
        fs.nodes['/usr/lib/ssl/openssl.cnf']['target'] = '/etc/passwd'
        self.assertEqual(run(fs)[1]['status'], 'ERROR')

    def test_ssl_both_original_spellings_reject_wrong_final(self):
        for path in core.SSL:
            with self.subTest(path=path):
                fs = ssl()
                fs.nodes[path] = dict(fs.nodes['/usr/lib/ssl/openssl.cnf'], target='/etc/ssl/other')
                self.assertEqual(run(fs, path)[1]['status'], 'ERROR')

    def test_ssl_no_subtree_grant(self):
        self.assertEqual(run(ssl(), '/etc/ssl/other')[1]['status'], 'ERROR')

    def test_nonroot_every_component(self):
        for path in ('/', '/usr', '/usr/lib', '/usr/lib/ssl', '/usr/lib/ssl/openssl.cnf', '/etc', '/etc/ssl', '/etc/ssl/openssl.cnf'):
            with self.subTest(path=path):
                fs = ssl(); fs.nodes[path]['st_uid'] = 1000
                self.assertEqual(run(fs)[1]['status'], 'ERROR')

    def test_nonroot_group_rejected(self):
        fs = ssl(); fs.nodes['/etc/ssl/openssl.cnf']['st_gid'] = 1000
        self.assertEqual(run(fs)[1]['status'], 'ERROR')

    def test_group_other_writable_every_directory_and_file(self):
        for path in ('/', '/usr', '/usr/lib/ssl', '/etc', '/etc/ssl', '/etc/ssl/openssl.cnf'):
            for mode in (0o020, 0o002):
                with self.subTest(path=path, mode=mode):
                    fs = ssl(); fs.nodes[path]['st_mode'] |= mode
                    self.assertEqual(run(fs)[1]['status'], 'ERROR')

    def test_regular_hardlink_rejected(self):
        fs = ssl(); fs.nodes['/etc/ssl/openssl.cnf']['st_nlink'] = 2
        self.assertEqual(run(fs)[1]['status'], 'ERROR')

    def test_symlink_hardlink_rejected(self):
        fs = ssl(); fs.nodes['/usr/lib/ssl/openssl.cnf']['st_nlink'] = 2
        self.assertEqual(run(fs)[1]['status'], 'ERROR')

    def test_ssl_loop_finite(self):
        fs = ssl()
        fs.nodes['/etc/ssl/openssl.cnf'] = dict(fs.nodes['/usr/lib/ssl/openssl.cnf'])
        self.assertIn('loop', run(fs)[1]['error'])

    def test_sixteen_hop_bound(self):
        fs = FS()
        for i in range(18):
            fs.add('/usr/lib/a'+str(i), stat.S_IFLNK | 0o777, target='/usr/lib/a'+str(i+1))
        self.assertIn('depth', run(fs, '/usr/lib/a0')[1]['error'])

    def test_entry_fd_replacement_race(self):
        fs = ssl()
        def replace(path):
            if path == '/etc/ssl/openssl.cnf':
                fs.nodes[path] = dict(fs.nodes[path], st_ino=999)
        fs.onopen = replace
        self.assertIn('entry/FD drift', run(fs)[1]['error'])

    def test_file_mutation_during_read(self):
        fs = ssl()
        fs.onread = lambda path: fs.nodes[path].update(st_ctime_ns=456)
        self.assertIn('descriptor drift', run(fs)[1]['error'])

    def test_ancestor_entry_replacement_after_read(self):
        fs = ssl()
        fs.onread = lambda path: fs.nodes.update({'/etc':dict(fs.nodes['/etc'], st_ino=999)})
        self.assertIn('chain entry drift', run(fs)[1]['error'])

    def test_symlink_retarget_after_read(self):
        fs = ssl()
        fs.onread = lambda path: fs.nodes['/usr/lib/ssl/openssl.cnf'].update(st_ctime_ns=999, target='/etc/passwd')
        self.assertIn('chain entry drift', run(fs)[1]['error'])

    def test_absent_retained(self):
        fs = ssl(); del fs.nodes['/etc/ssl/openssl.cnf']
        row = run(fs)[1]
        self.assertEqual(row['status'], 'ABSENT')
        self.assertEqual(row['failed_component'], '/etc/ssl/openssl.cnf')

    def test_file_size_and_admission_before_read(self):
        fs = ssl()
        self.assertEqual(run(fs, limit=5)[1]['status'], 'ERROR')
        fs = ssl()
        def deny(physical, s):
            raise ValueError('unique cap')
        self.assertEqual(run(fs, admit=deny)[1]['error'], 'unique cap')

    def test_localtime_zoneinfo_only(self):
        fs = FS(); fs.add('/usr/share/zoneinfo/Etc/UTC')
        fs.add('/etc/localtime', stat.S_IFLNK | 0o777, target='/usr/share/zoneinfo/Etc/UTC')
        self.assertEqual(run(fs, '/etc/localtime')[1]['status'], 'PINNED')
        fs.nodes['/etc/localtime']['target'] = '/etc/ssl/openssl.cnf'
        self.assertEqual(run(fs, '/etc/localtime')[1]['status'], 'ERROR')

    def test_loader_intermediate_prefix_only(self):
        fs = FS(); fs.add('/usr/lib/ld.so')
        fs.add('/lib64', stat.S_IFLNK | 0o777, target='usr/lib64')
        fs.add('/usr/lib64/ld.so', stat.S_IFLNK | 0o777, target='../lib/ld.so')
        self.assertEqual(run(fs, '/lib64/ld.so')[1]['status'], 'PINNED')
        self.assertEqual(run(fs, '/usr/lib64')[1]['status'], 'ERROR')

    def test_pyc_timestamp_hash_and_invalid_metadata(self):
        for flags, expected in ((0,'TIMESTAMP'),(1,'UNCHECKED_HASH'),(3,'CHECKED_HASH'),(2,'REJECTED_FLAGS'),(4,'REJECTED_FLAGS')):
            with self.subTest(flags=flags):
                raw = b'abcd'+flags.to_bytes(4,'little')+(123).to_bytes(4,'little')+(6).to_bytes(4,'little')
                header = core.pyc_header(raw)
                self.assertEqual(header['classification'], expected)
                self.assertIn('OPEN', header['executed_bytecode_equality'])
        self.assertEqual(core.pyc_header(b'abc')['classification'], 'REJECTED_SHORT_HEADER')

    def test_source_cache_timestamp_correspondence_no_body_equality(self):
        fs = ssl(); row = run(fs, '/etc/ssl/openssl.cnf')[1]
        header = core.pyc_header(b'abcd'+bytes(4)+(123).to_bytes(4,'little')+(6).to_bytes(4,'little'))
        result = core.correspondence({'x':dict(file='src',cached='cache')}, {'src':row,'cache':dict(status='PINNED',pyc=header)})[0]
        self.assertTrue(result['timestamp_size_match'])
        self.assertEqual(result['executed_bytecode_equality'], 'OPEN')

    def test_identity_or_hash_drift_stales_without_retrace(self):
        row = run(ssl(), '/etc/ssl/openssl.cnf')[1]
        plan = dict(paths=[dict(path='p',classification='FILE_CANDIDATE',old_pin=dict(row))])
        for key in ('identity','sha256','size','physical'):
            with self.subTest(key=key):
                changed = dict(row); changed[key] = 'different'
                result = core.association(plan, {'p':changed})
                self.assertEqual(result['oldtrace_association'], 'STALE')
                self.assertFalse(result['eligible_candidate'] or result['automatic_retrace'])
        result = core.association(plan, {'p':row})
        self.assertTrue(result['eligible_candidate'])
        self.assertIn('OPEN', result['open_fd_to_later_inode'])

    def test_missing_and_error_pins_ineligible(self):
        for status in ('ABSENT','ERROR','DIRECTORY','REJECTED_PYC_HEADER'):
            result = core.association(dict(paths=[dict(path='p',classification='FILE_CANDIDATE')]), {'p':dict(status=status)})
            self.assertFalse(result['eligible_candidate'])

    def test_alias_copy_count_and_sealed_mode(self):
        row = run(ssl())[1]
        plan = dict(candidate_template=dict(version='SbfLinux-tiny-v1'),tool_dependencies={},
                    paths=[dict(path='/usr/lib/ssl/openssl.cnf',classification='FILE_CANDIDATE',provenance=[])])
        result = core.candidate(plan, {'/usr/lib/ssl/openssl.cnf':row}, dict(eligible_candidate=True))
        self.assertEqual(result['copied_bytes'], 2*row['size'])
        self.assertEqual(len(result['manifest']['files']), 2)
        self.assertTrue(all(f['mode']==0o444 for f in result['manifest']['files']))
        row['size'] = 33*2**20
        self.assertFalse(core.candidate(plan, {'/usr/lib/ssl/openssl.cnf':row}, dict(eligible_candidate=True))['eligible_candidate'])

    def test_retained_negative_provenance_not_complete_chain(self):
        failure = PLAN['failed_partial_chain']
        self.assertEqual(failure['status'], 'FAILED')
        self.assertEqual(failure['error'], 'symlink outside explicit paths: /etc/ssl/openssl.cnf')
        self.assertNotIn('/etc/ssl/openssl.cnf', [c['path'] for c in failure['components']])
        self.assertEqual(PLAN['old_trace']['successful_opens'], 51)
        self.assertEqual(PLAN['old_trace']['distinct_open_paths'], 49)

    def test_finite_plan_exact_module_fields_and_no_false_opens(self):
        self.assertEqual(len(PLAN['module_fields']), 136)
        self.assertEqual(len(PLAN['modules']), 68)
        for name, module in PLAN['modules'].items():
            for field in ('file','cached'):
                matches = [r for r in PLAN['module_fields'] if r['module']==name and r['field']==field]
                self.assertEqual(len(matches), 1)
                self.assertEqual(matches[0]['path'], module[field])
        rows = {r['path']:r for r in PLAN['paths']}
        self.assertFalse(rows['/etc/ssl/openssl.cnf']['observed_open'])
        self.assertTrue(rows['/usr/lib/ssl/openssl.cnf']['observed_open'])
        self.assertNotIn('/usr/bin/strace', rows)
        self.assertTrue(any(r['classification']=='PROSPECTIVE_FALLBACK' for r in PLAN['module_fields']))
        self.assertEqual(sum(r['observed_open'] for r in PLAN['paths']), 49)

    def test_payload_guard_bytes_ast_globals_no_execution_sites(self):
        guard = (HERE/'SbfRuntimeFinish-guard.py.txt').read_bytes()
        payload = (HERE/'SbfRuntimeFinish_payload.py.txt').read_bytes()
        self.assertEqual(hashlib.sha256(guard).hexdigest(), '9f0fbfd713895348a3df87fb4bb8643a85a4facb1d5ce95e31ad7839db74ca6d')
        self.assertEqual(len(guard), 8426)
        self.assertTrue(payload.startswith(guard))
        self.assertEqual(payload.count(guard), 1)
        gt, pt = ast.parse(guard), ast.parse(payload)
        self.assertEqual(ast.dump(gt), ast.dump(ast.Module(body=pt.body[:len(gt.body)],type_ignores=[])))
        later = ast.Module(body=pt.body[len(gt.body):],type_ignores=[])
        protected = {'BUDGET','INTERVAL','MAX_SAMPLES','MAX_LINEAGE','Guard','GuardError','Proc','inherited_limits','check_limits'}
        for n in ast.walk(later):
            if isinstance(n,(ast.FunctionDef,ast.ClassDef)):
                self.assertNotIn(n.name, protected)
            if isinstance(n,ast.Name) and isinstance(n.ctx,ast.Store):
                self.assertNotIn(n.id, protected)
        forbidden = {'Popen','run','call','check_output','system','fork','execve','execv','posix_spawn','setrlimit','prlimit','CDLL','PyDLL','load','loads'}
        # json.loads is absent too: finite plan is a literal, not runtime input.
        for n in ast.walk(pt):
            if isinstance(n,ast.Call):
                if isinstance(n.func,ast.Attribute): self.assertNotIn(n.func.attr, forbidden)
                if isinstance(n.func,ast.Name): self.assertNotIn(n.func.id, {'exec','eval','__import__'})
            if isinstance(n,ast.Import):
                self.assertTrue(all(a.name not in {'subprocess','ctypes','marshal'} for a in n.names))
        self.assertEqual(sum(isinstance(n,ast.Call) and isinstance(n.func,ast.Attribute) and n.func.attr=='alarm' and n.args and isinstance(n.args[0],ast.Constant) and n.args[0].value==115 for n in ast.walk(pt)), 1)
        self.assertEqual(PLAN['bounds']['prospective_ssh_seconds'], 120)
