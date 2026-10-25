"""Prospective payload checks. OS/transport replaced; never call actual setup."""
import ast
import base64
import copy
import hashlib
import json
import os
from pathlib import Path
import stat
from types import SimpleNamespace as NS
import unittest
from unittest.mock import Mock,patch

D=Path(__file__).resolve().parent
R=D/'prospective-data-v2'

def receiver():
    ns={'__name__':'source_review_only'}
    exec((R/'FinalNativeGate-data-transfer.py').read_bytes(),ns)
    return ns

class Tree:
    def __init__(self,ns):
        self.nodes={};self.fds={};self.counter=100;self.fail_close=False;self.hardlink=False
        current=''
        for part in ['',*ns['STAGE'].split('/')[1:-1]]:
            current=(current+'/'+part) if current else '/'
            current=current.replace('//','/')
            self.nodes[current]=dict(mode=0o40755,raw=bytearray(),uid=123)
        self.api=NS(**{k:getattr(os,k) for k in ('O_RDONLY','O_WRONLY','O_DIRECTORY','O_NOFOLLOW','O_NONBLOCK','O_CREAT','O_EXCL')},
            getuid=lambda:123,open=self.open,close=self.close,stat=self.stat,fstat=self.fstat,mkdir=self.mkdir,write=self.write,read=self.read,fsync=lambda fd:None)
    def path(self,name,dir_fd=None):
        if dir_fd is None:return str(name)
        return self.fds[dir_fd][0].rstrip('/')+'/'+name
    def stat(self,name,dir_fd=None,follow_symlinks=False):
        path=self.path(name,dir_fd)
        if path not in self.nodes:raise FileNotFoundError(path)
        row=self.nodes[path]
        return NS(st_dev=1,st_ino=list(self.nodes).index(path)+1,st_mode=row['mode'],st_uid=row['uid'],st_gid=123,
            st_size=len(row['raw']),st_nlink=2 if self.hardlink and stat.S_ISREG(row['mode']) else 1)
    def fstat(self,fd):return self.stat(self.fds[fd][0])
    def open(self,name,flags,mode=0o777,dir_fd=None):
        path=self.path(name,dir_fd)
        if not flags&os.O_NOFOLLOW:raise AssertionError('missing nofollow')
        if flags&os.O_CREAT:
            if path in self.nodes:raise FileExistsError(path)
            if not flags&os.O_EXCL:raise AssertionError('missing exclusive')
            self.nodes[path]=dict(mode=stat.S_IFREG|mode,raw=bytearray(),uid=123)
        if path not in self.nodes:raise FileNotFoundError(path)
        if stat.S_ISLNK(self.nodes[path]['mode']):raise OSError('symlink')
        self.counter+=1;self.fds[self.counter]=[path,0,bool(flags&os.O_WRONLY)]
        return self.counter
    def close(self,fd):
        path,offset,writer=self.fds.pop(fd)
        if writer and self.fail_close:self.nodes[path]['raw'][:1]=b'!'
    def mkdir(self,name,mode,dir_fd):
        path=self.path(name,dir_fd)
        if path in self.nodes:raise FileExistsError(path)
        self.nodes[path]=dict(mode=stat.S_IFDIR|mode,raw=bytearray(),uid=123)
    def write(self,fd,raw):self.nodes[self.fds[fd][0]]['raw'].extend(raw);return len(raw)
    def read(self,fd,n):
        path,at,_=self.fds[fd];raw=bytes(self.nodes[path]['raw'][at:at+n]);self.fds[fd][1]+=len(raw);return raw

class Release(unittest.TestCase):
    def test_exact_activated_bytes_seals_and_only_two_entry_deltas(self):
        ns=receiver();rows=ns['decoded']();ns['verify'](rows)
        identity=json.loads((R/'FinalNativeGate-release-identities.json').read_bytes())
        for name,raw in rows.items():self.assertEqual(raw,(R/'payload'/name).read_bytes())
        for name in ('FinalNativeGate.py','FinalNativeGate_inside.py'):
            self.assertEqual(rows[name],(D/name).read_bytes())
        for name in ('FinalNativeGate.py','FinalNativeGate_inside.py','FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py'):
            main=next(n for n in ast.parse((D/name).read_bytes()).body if isinstance(n,ast.FunctionDef) and n.name=='main')
            self.assertEqual(len(main.body),2);self.assertEqual(main.body[-1].value.value,78)
        for name,row in identity['function_identities'].items():
            self.assertEqual(row['changed'],['main'] if name in ('FinalNativeGate_setup.py','FinalNativeGate_setup_inside.py') else [])
        self.assertTrue(identity['no_final_charge_authority'])
        p=json.loads(rows['FinalNativeGate-plan.json']);original=json.loads((D/'FinalNativeGate-plan.json').read_bytes())
        stage=ns['STAGE']+'/'
        self.assertEqual({k:v for k,v in p['files'].items() if not k.startswith(stage)},
                         {k:v for k,v in original['files'].items() if not k.startswith(stage)})
        for key in p:
            if key not in ('files','job_source_sizes','job_revision','setup_catalog_roots'):self.assertEqual(p[key],original[key],key)

    def test_receiver_exclusive_copy_closed_writer_and_packet_creation(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api
        result=ns['install']();self.assertFalse(tree.fds)
        self.assertEqual(result['status'],'FIXED_DATA_SOURCE_TRANSFERRED')
        self.assertFalse(result['execution_authority'])
        for name,raw in ns['decoded']().items():
            row=tree.nodes[ns['STAGE']+'/'+name];self.assertEqual(bytes(row['raw']),raw);self.assertEqual(row['mode'],0o100600)
        # Packet directory changes no code-file bytes/identities.
        before={n:bytes(v['raw']) for n,v in tree.nodes.items() if stat.S_ISREG(v['mode'])}
        fd=tree.open(ns['STAGE'],os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
        tree.mkdir('FinalNativeGate-setup-packet',0o700,fd);tree.close(fd)
        self.assertEqual(before,{n:bytes(tree.nodes[n]['raw']) for n in before})
        with self.assertRaises(FileExistsError):ns['install']()
        self.assertFalse(tree.fds)

    def test_receiver_ancestry_alias_refused(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api
        tree.nodes['/home']['mode']=0o120777
        with self.assertRaisesRegex(ValueError,'ancestor'):ns['install']()
        self.assertNotIn(ns['STAGE'],tree.nodes);self.assertFalse(tree.fds)

    def test_receiver_wrong_parent_owner_refused(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api
        tree.nodes[ns['STAGE'].rsplit('/',1)[0]]['uid']=0
        with self.assertRaisesRegex(ValueError,'user owned'):ns['install']()
        self.assertNotIn(ns['STAGE'],tree.nodes)

    def test_receiver_failed_closed_writer_hash_retains_partial(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api;tree.fail_close=True
        with self.assertRaisesRegex(ValueError,'source drift'):ns['install']()
        self.assertIn(ns['STAGE'],tree.nodes)
        self.assertTrue(any(n.startswith(ns['STAGE']+'/') for n in tree.nodes));self.assertFalse(tree.fds)

    def test_receiver_hardlink_refused_retains_partial(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api;tree.hardlink=True
        with self.assertRaisesRegex(ValueError,'single-link'):ns['install']()
        self.assertIn(ns['STAGE'],tree.nodes);self.assertFalse(tree.fds)

    def test_receiver_pinned_bytes_and_seal_corruption_rejected(self):
        ns=receiver();rows=ns['decoded']();rows['FinalNativeGate_seal.py']=b'wrong'
        with self.assertRaisesRegex(ValueError,'plan seal'):ns['verify'](rows)
        first=next(iter(ns['FILES']));ns['FILES'][first]['b85']=base64.b85encode(b'bad').decode()
        with self.assertRaisesRegex(ValueError,'pinned bytes'):ns['decoded']()

    def test_receiver_limits_before_decode_or_write(self):
        ns=receiver();first=next(iter(ns['FILES']));ns['FILES'][first]['size']=4*2**20+1
        with self.assertRaisesRegex(ValueError,'per-file bound'):ns['decoded']()

    def packet(self):
        ns=receiver();tree=Tree(ns);ns['os']=tree.api
        ns['install']()
        fd=tree.open(ns['STAGE'],os.O_RDONLY|os.O_DIRECTORY|os.O_NOFOLLOW)
        tree.mkdir('FinalNativeGate-setup-packet',0o700,fd);tree.close(fd)
        for name in ('FinalNativeGate-setup-terminal.json','FinalNativeGate-setup-parent-terminal.json',
                     'FinalNativeGate-candidate-controls.json','FinalNativeGate-setup-parent-cleanup.json','FinalNativeGate-setup-parent-guard.json'):
            tree.nodes[ns['STAGE']+'/FinalNativeGate-setup-packet/'+name]=dict(mode=0o100600,raw=bytearray(json.dumps({'role':name,'execution_authority':False}).encode()),uid=123)
        return ns,tree

    def test_fixed_packet_summary_public_records_and_hash_only_cleanup(self):
        ns,tree=self.packet();summary=ns['packet_summary']()
        self.assertEqual(len(summary),5)
        self.assertEqual(summary['FinalNativeGate-candidate-controls.json']['record']['role'],'FinalNativeGate-candidate-controls.json')
        self.assertNotIn('record',summary['FinalNativeGate-setup-parent-cleanup.json'])
        for name,row in summary.items():
            raw=bytes(tree.nodes[ns['STAGE']+'/FinalNativeGate-setup-packet/'+name]['raw'])
            self.assertEqual(row['sha256'],hashlib.sha256(raw).hexdigest());self.assertEqual(row['size'],len(raw))
        self.assertFalse(tree.fds)

    def test_fixed_packet_missing_file_exact_partial_error(self):
        ns,tree=self.packet()
        del tree.nodes[ns['STAGE']+'/FinalNativeGate-setup-packet/FinalNativeGate-candidate-controls.json']
        summary=ns['packet_summary']()
        self.assertIn('FinalNativeGate-candidate-controls.json',summary['FinalNativeGate-candidate-controls.json']['error'])
        self.assertIn('record',summary['FinalNativeGate-setup-terminal.json']);self.assertFalse(tree.fds)

    def test_packet_alias_refused(self):
        ns,tree=self.packet();tree.nodes[ns['STAGE']+'/FinalNativeGate-setup-packet']['mode']=0o120777
        with self.assertRaisesRegex(ValueError,'ancestor'):ns['packet_summary']()
        self.assertFalse(tree.fds)

    def test_literal_outer_transport_without_execution(self):
        ns={'__name__':'source_review_only'}
        exec((R/'FinalNativeGate-data-transport.py').read_bytes(),ns)
        self.assertEqual(ns['ARGV'][-2:],['dombarker@100.108.41.90','/usr/bin/python3 -I -B -'])
        self.assertEqual(ns['PIN']['sha256'],hashlib.sha256((R/'FinalNativeGate-data-transfer.py').read_bytes()).hexdigest())
        text=(R/'FinalNativeGate-data-transport.py').read_text()
        self.assertIn('>120',text);self.assertEqual(ns['LIMIT'],4*2**20)
        self.assertNotIn('shell=True',text)
        # Only receiver main may launch setup; no final call in receiver AST.
        calls=[n for n in ast.walk(ast.parse((R/'FinalNativeGate-data-transfer.py').read_bytes())) if isinstance(n,ast.Call)]
        self.assertFalse(any(isinstance(n.func,ast.Name) and n.func.id in ('_execute','_charge') for n in calls))

if __name__=='__main__':unittest.main(verbosity=2)
