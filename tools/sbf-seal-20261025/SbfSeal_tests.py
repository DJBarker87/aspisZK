"""Ordinary path tests and explicitly synthetic metadata; no privileged backend."""
import copy
import errno
import hashlib
import json
import os
from pathlib import Path
import stat
import tempfile
import unittest
from unittest.mock import patch
import SbfSeal_setup as s
import SbfSeal_admission as a
import SbfSeal_boundary as b


def pin(raw=b'public'):
    return dict(sha256=hashlib.sha256(raw).hexdigest(), size=len(raw), mode=0o444)


class Paths(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='SbfSeal-ordinary-')
        self.path = Path(self.temp.name)
        self.fd = os.open(self.path, s.DIR_FLAGS)
        self.owner = os.getuid()
        self.capture = s.Capture(self.fd, self.owner)

    def tearDown(self):
        # Only ordinary caller-owned test directories. No key/material cleanup.
        for fd in self.capture.dirs.values():
            os.fchmod(fd, 0o700)
        self.capture.close()
        os.close(self.fd)
        self.temp.cleanup()

    def source(self, raw=b'public'):
        p = self.path/'input'
        p.write_bytes(raw)
        return s.open_source(str(p))

    def test_copy_and_seal(self):
        src = self.source()
        try:
            self.capture.copy(src, '/usr/lib/public', pin())
            self.assertNotEqual(s.inode(os.fstat(src)), s.inode(os.fstat(self.capture.files['/usr/lib/public']['fd'])))
            self.capture.seal()
            self.assertEqual((self.path/'usr/lib/public').read_bytes(), b'public')
            self.assertEqual(stat.S_IMODE((self.path/'usr/lib/public').stat().st_mode), 0o444)
            self.assertIsNone(self.capture.files['/usr/lib/public']['fd'])
            with self.assertRaises(s.Denied): self.capture.copy(src, '/later', pin())
        finally: os.close(src)

    def test_all_components_nofollow(self):
        (self.path/'real').mkdir()
        (self.path/'real/file').write_bytes(b'public')
        (self.path/'link').symlink_to('real', target_is_directory=True)
        with self.assertRaises(OSError): s.open_source(str(self.path/'link/file'))
        (self.path/'filelink').symlink_to('real/file')
        with self.assertRaises(OSError): s.open_source(str(self.path/'filelink'))

    def test_source_hardlink_rejected(self):
        (self.path/'input').write_bytes(b'public')
        os.link(self.path/'input', self.path/'alias')
        with self.assertRaises(s.Denied): s.open_source(str(self.path/'input'))

    def test_wrong_directory_owner_before_write(self):
        with self.assertRaises(s.Denied): s.exclusive_dir(self.fd, 'must-not-exist', self.owner+1)
        self.assertFalse((self.path/'must-not-exist').exists())

    def test_writable_directory_before_write(self):
        os.fchmod(self.fd, 0o777)
        try:
            with self.assertRaises(s.Denied): s.exclusive_dir(self.fd, 'no-write', self.owner)
            self.assertFalse((self.path/'no-write').exists())
        finally: os.fchmod(self.fd, 0o700)

    def test_exclusive_directory_and_file(self):
        child = s.exclusive_dir(self.fd, 'existing', self.owner)
        os.close(child)
        with self.assertRaises(FileExistsError): s.exclusive_dir(self.fd, 'existing', self.owner)
        src = self.source()
        try:
            (self.path/'existing-file').write_bytes(b'original')
            with self.assertRaises(FileExistsError): self.capture.copy(src, '/existing-file', pin())
            self.assertEqual((self.path/'existing-file').read_bytes(), b'original')
        finally: os.close(src)

    def test_destination_symlink_denies_before_target_write(self):
        (self.path/'victim').mkdir()
        (self.path/'usr').symlink_to('victim', target_is_directory=True)
        src = self.source()
        try:
            with self.assertRaises(FileExistsError): self.capture.copy(src, '/usr/file', pin())
            self.assertEqual(list((self.path/'victim').iterdir()), [])
        finally: os.close(src)

    def test_parent_replaced_detected_before_write(self):
        self.capture.parent('/usr/first')
        (self.path/'usr').rename(self.path/'old')
        (self.path/'usr').mkdir()
        src = self.source()
        try:
            with self.assertRaises(s.Denied): self.capture.copy(src, '/usr/second', pin())
            self.assertFalse((self.path/'usr/second').exists())
            self.assertFalse((self.path/'old/second').exists())
        finally: os.close(src)

    def test_renamed_root_fd_does_not_write_replacement(self):
        # Simulates same-uid adversary (excluded by future ROOT ancestry premise).
        # The test asserts fd anchoring, NOT prevention of privileged root rename.
        src = self.source()
        oldpath = self.path.with_name(self.path.name+'-retained')
        self.path.rename(oldpath)
        self.path.mkdir(mode=0o700)
        try:
            self.capture.copy(src, '/file', pin())
            self.assertFalse((self.path/'file').exists())
            self.assertEqual((oldpath/'file').read_bytes(), b'public')
        finally:
            os.close(src)
            self.path.rmdir()
            oldpath.rename(self.path)

    def test_source_digest_change_retains_failure(self):
        src = self.source(b'wrong!')
        try:
            with self.assertRaises(s.Denied): self.capture.copy(src, '/failed', pin())
            self.assertTrue((self.path/'failed').exists())
            self.assertFalse(self.capture.sealed)
        finally: os.close(src)

    def test_source_changed_midcopy(self):
        src = self.source()
        real_read = os.read
        once = []
        def mutate(fd, size):
            raw = real_read(fd, size)
            if fd == src and not once:
                once.append(True)
                (self.path/'input').write_bytes(b'public-modified')
            return raw
        try:
            with patch.object(s.os, 'read', side_effect=mutate):
                with self.assertRaises(s.Denied): self.capture.copy(src, '/failed', pin())
        finally: os.close(src)

    def test_destination_hardlink_detected_at_seal(self):
        src = self.source()
        try:
            self.capture.copy(src, '/file', pin())
            os.link(self.path/'file', self.path/'alias')
            with self.assertRaises(s.Denied): self.capture.seal()
        finally: os.close(src)

    def test_invalid_paths_before_effects(self):
        for p in ('relative','/','/a/../b','/a//b','/a/./b','/a\x00b','/a b'):
            with self.subTest(path=p):
                with self.assertRaises(s.Denied): self.capture.parent(p)
        self.assertEqual(list(self.path.iterdir()), [])


class OutputTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='SbfSeal-output-')
        self.path = Path(self.temp.name)
        self.fd = os.open(self.path, s.DIR_FLAGS)
        self.out = s.PublicOutput(self.fd, os.getuid())

    def tearDown(self):
        self.out.close(); os.close(self.fd); self.temp.cleanup()

    def write_public(self):
        raw = (json.dumps({'SbfSeal':'tiny-public-v1','uid':1000,'gid':1000,'fds':[0,1,2]},sort_keys=True)+'\n').encode()
        os.write(self.out.rows['stdout']['w'], raw)

    def test_collect_exact_public_after_wait(self):
        self.write_public(); self.out.close_writers()
        self.assertIn('tiny-public-v1', self.out.collect(123,123,0)['stdout'])

    def test_actual_wait_route_mocked_not_a_child_execution(self):
        self.write_public()
        with patch.object(s.os,'waitpid',return_value=(123,0)) as wait:
            result = self.out.wait_and_collect(123)
        wait.assert_called_once_with(123,os.WNOHANG)
        self.assertIn('tiny-public-v1',result['stdout'])

    def test_wait_unknown_or_wrong_child_denies_export(self):
        self.write_public()
        with patch.object(s.os,'waitpid',return_value=(124,0)):
            with self.assertRaises(s.Denied): self.out.wait_and_collect(123)

    def test_parent_writer_denied(self):
        self.write_public()
        with self.assertRaises(s.Denied): self.out.collect(123,123,0)

    def test_wait_failures(self):
        self.write_public(); self.out.close_writers()
        for waited, status in ((124,0),(123,256),(123,9)):
            with self.assertRaises(s.Denied): self.out.collect(waited,123,status)

    def test_overflow(self):
        os.write(self.out.rows['stdout']['w'], b'x'*(s.OUTPUT_BOUND+1))
        self.out.close_writers()
        with self.assertRaises(s.Denied): self.out.collect(123,123,0)

    def test_inode_replace(self):
        self.write_public(); self.out.close_writers()
        (self.path/'stdout').rename(self.path/'retained')
        (self.path/'stdout').write_bytes(b'forged')
        with self.assertRaises(s.Denied): self.out.collect(123,123,0)

    def test_output_hardlink(self):
        self.write_public(); self.out.close_writers()
        os.link(self.path/'stdout', self.path/'alias')
        with self.assertRaises(s.Denied): self.out.collect(123,123,0)

    def test_nonpublic_and_stderr(self):
        os.write(self.out.rows['stdout']['w'], b'not the public schema')
        os.write(self.out.rows['stderr']['w'], b'error')
        self.out.close_writers()
        with self.assertRaises(s.Denied): self.out.collect(123,123,0)


def manifest():
    return dict(version='SbfSeal-tiny-v1',root=s.ROOT,uid=1000,gid=1000,argv=list(s.PROBE),env=dict(s.ENV),
                files=[dict(logical='/usr/bin/python3',physical='/public/python3',**pin())])


def report():
    ident = dict(pid=123,starttime=987,unified_path='/user.slice/'+a.UNIT,
                 path='/sys/fs/cgroup/user.slice/'+a.UNIT)
    binding = dict(self_identity=ident,expected_limits=a.EXPECTED,observed_limits=a.EXPECTED,
                   ancestor_limits=[dict(path='/sys/fs/cgroup',cap=None,high=None)],
                   finite_frontier_association=ident['path'])
    snapshot = dict(rows=[{'not_a_real_scan':True}],self_observation=dict(ident,reads=[]))
    return dict(api_version='ResourceRssGO20261025-v1',collector_pid=123,
                decision=dict(schema='ResourceStability20261025-v1',phase='inside-scope',
                              additional_bytes=0,allowed=True,collector_identity=ident,scope_binding=binding),
                snapshots=dict(before=snapshot,after=copy.deepcopy(snapshot)),original_legacy={},print_axioms='N/A')


def projection(r=None):
    # Explicitly synthetic: even incomplete full tree is never authority.
    return a.project(json.dumps(report() if r is None else r).encode(), a.PRODUCER_PIN)


class Synthetic(unittest.TestCase):
    def test_manifest_exact_mutations(self):
        self.assertEqual(len(s.validate_manifest(manifest())['sha256']), 64)
        mutations = [('uid',0),('gid',0),('root','/tmp/arbitrary'),('argv',['/bin/sh']),
                     ('env',{'PATH':'/bin'}),('extra',True),('files',[])]
        for k,v in mutations:
            m = manifest(); m[k] = v
            with self.subTest(field=k):
                with self.assertRaises(s.Denied): s.validate_manifest(m)
        for k,v in [('physical','/a/../b'),('logical','/etc/../shadow'),('sha256','z'*64),('mode',0o777),('size',-1)]:
            m = manifest(); m['files'][0][k] = v
            with self.subTest(field=k):
                with self.assertRaises(s.Denied): s.validate_manifest(m)

    def test_disabled_before_any_effect(self):
        effects = []
        with patch.object(s.os,'mkdir',side_effect=lambda *args,**kwargs: effects.append(args)):
            with self.assertRaises(s.Denied): s.privileged_entrypoint()
            with self.assertRaises(s.Denied): a.fresh_host_admission()
            with self.assertRaises(s.Denied): b.linux_setup()
        self.assertEqual(effects, [])
        with self.assertRaises(TypeError): s.privileged_entrypoint(['/bin/sh'])

    def test_root_ancestry_unknown_denies_before_write(self):
        # Mock metadata ONLY: tests check validation-before-mkdir, not real root.
        with tempfile.TemporaryDirectory(prefix='SbfSeal-ancestry-') as p:
            with patch.object(s,'check_dir',side_effect=s.Denied('synthetic unsafe ancestor')):
                with patch.object(s.os,'mkdir',side_effect=AssertionError('effect before check')):
                    with self.assertRaises(s.Denied): s.open_safe_ancestry(p)

    def test_projection_is_never_admission(self):
        p = projection()
        self.assertFalse(p['authorized'])
        self.assertIn('not replayed',p['status'])
        raw = json.dumps(report()).encode()
        self.assertEqual(p['raw_report'],s.digest(raw))
        with self.assertRaises(s.Denied): a.fresh_host_admission()

    def test_go_schema_and_count_errors(self):
        for key,value in [('api_version','fake'),('collector_pid',True),('decision',{'allowed':True}),
                          ('snapshots',{}),('original_legacy',None)]:
            r = report(); r[key] = value
            with self.subTest(field=key):
                with self.assertRaises((s.Denied, KeyError)): projection(r)
        for key,value in [('allowed',False),('additional_bytes',4*2**30),('phase','old'),('error','failure')]:
            r = report(); r['decision'][key] = value
            with self.assertRaises(s.Denied): projection(r)
        r = report(); r['decision']['scope_binding']['observed_limits'] = dict(a.EXPECTED,swap_max=1)
        with self.assertRaises(s.Denied): projection(r)
        with self.assertRaises(s.Denied): a.parse_report(b'{"allowed":true}')
        with self.assertRaises(s.Denied): a.parse_report(b'{"x":1,"x":2}')
        with self.assertRaises(s.Denied): a.parse_report(b'{"x":NaN}')
        with self.assertRaises(s.Denied): a.project(b'{}',{})

    def test_ancestry_model_sudo_intermediate(self):
        p = projection(); chain=[]; pins={}
        for i, role in enumerate(('collector','sudo','helper')):
            pins[role] = {'sha256':str(i)*64,'size':100}
            caps = dict(Inh=0,Prm=0 if i==0 else (1<<40)-1,Eff=0 if i==0 else (1<<40)-1,Bnd=(1<<40)-1,Amb=0)
            chain.append(dict(role=role,pid=123+i,ppid=10 if i==0 else 122+i,starttime=987+i,
                              cgroup=p['collector']['unified_path'],exe=pins[role],uid=[1000]*3 if i==0 else [0]*3,
                              gid=[1000]*3 if i==0 else [0]*3,caps=caps))
        self.assertFalse(a.check_ancestry(chain,copy.deepcopy(chain),p,pins)['authorized'])
        for key,value in [('ppid',999),('cgroup','/wrong'),('caps',{}),('uid',[1000]*3),('starttime',0)]:
            bad=copy.deepcopy(chain); bad[-1][key]=value
            with self.subTest(field=key):
                with self.assertRaises(s.Denied): a.check_ancestry(bad,copy.deepcopy(bad),p,pins)
        bad=copy.deepcopy(chain); bad[-1]['starttime']+=1
        with self.assertRaises(s.Denied): a.check_ancestry(chain,bad,p,pins)
        with self.assertRaises(s.Denied): a.check_ancestry(chain[::2],chain[::2],p,pins)

    def test_guest_metadata_fd3_caps_abi_namespace_denials(self):
        expect=dict(cgroup='/fixed',root_inode=[1,2],host_ns=dict(mnt=1,net=2,pid=3),
                    guest_ns=dict(mnt=4,net=5,pid=6),mounts=['synthetic ro private proc'])
        obs=dict(abi='linux-x86_64-capv3',namespaces=expect['guest_ns'],uid=[1000]*3,gid=[1000]*3,
                 groups=[],caps=dict(Inh=0,Prm=0,Eff=0,Bnd=0,Amb=0),nnp=1,fds=[0,1,2],cgroup='/fixed',
                 root_inode=[1,2],mounts=expect['mounts'],limits={'nofile':[256,256],'fsize':[16384,16384]})
        self.assertFalse(b.check_guest(obs,expect)['authorized'])
        for key,value in [('fds',[0,1,2,3]),('abi','darwin'),('nnp',0),('caps',dict(Inh=0,Prm=0,Eff=1,Bnd=0,Amb=0)),
                          ('namespaces',expect['host_ns']),('groups',[1000]),('mounts',[])]:
            bad=copy.deepcopy(obs); bad[key]=value
            with self.subTest(field=key):
                with self.assertRaises(s.Denied): b.check_guest(bad,expect)

    def test_trace_fixture_obstructions(self):
        data=json.loads((Path(__file__).parents[2]/'evidence/sbf-seal-20261025/SbfSeal-trace-fixtures.json').read_text())
        self.assertEqual(set(data['fixtures']),{'shared-state','wait','negative-probe','unfinished','resumed','loader-cache','pyc'})
        patterns={'shared-state':'CLONE_','wait':'wait4(', 'negative-probe':'ENOENT',
                  'unfinished':'<unfinished', 'resumed':'resumed>', 'loader-cache':'ld.so.cache', 'pyc':'.pyc'}
        for name,row in data['fixtures'].items():
            self.assertIn(patterns[name],row['line'])
            self.assertTrue(row['unsupported_reason'])
