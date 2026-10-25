"""New report fixtures only; private retained trees and explicit syscall mocks."""
import ast, hashlib, importlib.util, json, os, resource, stat, subprocess, tempfile, unittest
from pathlib import Path
from types import SimpleNamespace
from unittest.mock import patch
D=Path(__file__).resolve().parent

def load(name,file):
    spec=importlib.util.spec_from_file_location(name,D/file)
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

diag=load('admission_report','FinalNativeGate-admission-report.py')
t=load('admission_transport','FinalNativeGate-admission-report-transport.py')

class Report(unittest.TestCase):
    def setUp(self):
        self.root=Path(tempfile.mkdtemp(prefix='FinalNativeGate-admission-report-012-',dir='/private/tmp'))
        print('retained_private_fixture='+str(self.root))
        self.parts=('home','user','stage','packet');p=self.root
        for part in self.parts:p=p/part;p.mkdir(mode=0o700)
        self.packet=p;self.file=p/diag.NAMES[0]
        fd=os.open(self.file,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
        with os.fdopen(fd,'wb') as f:f.write(b'{"decision":{"allowed":false,"reasons":["capacity denied"]},"phase":"prospective","collection_failures":["fixture visibility"],"raw_receipts":[{"name":"never read"}],"original_legacy":{"secret":"OMIT"},"process_visibility":"OMIT","orderedinput":"OMIT","env":"OMIT"}')
        self.real_open=os.open;self.real_stat=os.stat;self.real_fstat=os.fstat
    def raw(self,raw):
        with self.file.open('wb') as f:f.write(raw)
    def observe(self,fault=None):
        opened=[];closed=[];calls={};real_close=os.close;real_read=os.read
        def op(path,flags,*args,**kwargs):
            self.assertFalse(flags&(os.O_WRONLY|os.O_RDWR|os.O_CREAT))
            if path=='/':path=self.root
            fd=self.real_open(path,flags,*args,**kwargs);opened.append(fd);return fd
        def close(fd):closed.append(fd);return real_close(fd)
        def modified(s,key):
            row={k:getattr(s,k) for k in dir(s) if k.startswith('st_')};row[key]+=1
            return SimpleNamespace(**row)
        alias_stamp=None
        def aliased(s):
            nonlocal alias_stamp
            if stat.S_ISDIR(s.st_mode):
                if alias_stamp is None and s.st_ino!=self.real_stat(self.root).st_ino:alias_stamp=s
                elif alias_stamp is not None:
                    row={k:getattr(s,k) for k in dir(s) if k.startswith('st_')}
                    row['st_dev']=alias_stamp.st_dev;row['st_ino']=alias_stamp.st_ino
                    return SimpleNamespace(**row)
            return s
        def fs(fd):
            s=self.real_fstat(fd);calls[fd]=calls.get(fd,0)+1
            if fault=='alias':s=aliased(s)
            if stat.S_ISREG(s.st_mode):
                if fault=='owner':return modified(s,'st_uid')
                if fault=='fd-drift' and calls[fd]>=2:return modified(s,'st_ctime_ns')
            return s
        entries={}
        def entry(path,*args,**kw):
            s=self.real_stat(path,*args,**kw);entries[path]=entries.get(path,0)+1
            if path==diag.NAMES[0] and fault=='entry-drift' and entries[path]>=2:return modified(s,'st_mtime_ns')
            if fault=='alias':s=aliased(s)
            return s
        reads=0
        def read(fd,count):
            nonlocal reads
            reads+=1
            if fault=='read-error':raise OSError('fixture partial read error')
            if fault=='partial' and reads>1:return b''
            return real_read(fd,1 if fault=='partial' else count)
        with patch.object(diag,'CHAIN',self.parts),patch.object(diag.os,'open',op),patch.object(diag.os,'close',close),patch.object(diag.os,'fstat',fs),patch.object(diag.os,'stat',entry),patch.object(diag.os,'read',read):
            r=diag.collect()
        self.assertEqual(sorted(opened),sorted(closed));self.assertLessEqual(len(opened),6)
        return r
    def row(self,**kw):return self.observe(**kw)['files'][diag.NAMES[0]]
    def test_actual_shape_denial_only_selected_and_hashes(self):
        r=self.observe();row=r['files'][diag.NAMES[0]]
        self.assertTrue(r['interval_stable']);self.assertFalse(r['trusted']);self.assertFalse(r['GO'])
        self.assertEqual(set(row['selected_fields']),{'decision','collection_failures','phase'})
        self.assertEqual(row['selected_fields']['decision']['value']['reasons'],['capacity denied'])
        self.assertEqual(row['sha256'],hashlib.sha256(self.file.read_bytes()).hexdigest())
        for x in row['selected_fields'].values():
            raw=json.dumps(x['value'],sort_keys=True,ensure_ascii=True,allow_nan=False,separators=(',',':')).encode()
            self.assertEqual((x['size'],x['sha256']),(len(raw),hashlib.sha256(raw).hexdigest()))
        self.assertNotIn('OMIT',json.dumps(r));self.assertNotIn('raw_receipts',json.dumps(r))
    def test_concrete_decision_embedded_legacy_and_failure_inputs_omitted(self):
        value=dict(decision=dict(allowed=False,error='legacy visibility error/missing',
                   legacy=dict(process_visibility='OMIT'),before_observation={'raw':'OMIT'},
                   reasons=[{'env':'OMIT','reason':'bounded reason'}],
                   collection_failures=dict(before=dict(error='fixture denied',type='ValueError',
                        raw_inputs={'env':'OMIT'},read_attempts=['OMIT']))),
                   original_legacy={'raw':'OMIT'})
        self.raw(json.dumps(value).encode());row=self.row();fields=row['selected_fields']
        self.assertNotIn('OMIT',json.dumps(fields))
        self.assertEqual(fields['decision']['value']['collection_failures']['before']['error'],'fixture denied')
        raw=json.dumps(value['decision'],sort_keys=True,ensure_ascii=True,allow_nan=False,separators=(',',':')).encode()
        self.assertEqual(fields['decision']['sha256'],hashlib.sha256(raw).hexdigest())
    def test_groupwrite_original_fail_untrusted(self):
        os.chmod(self.file,0o664);row=self.row()
        self.assertFalse(row['original_receiver_predicate']);self.assertTrue(row['group_write_exception']);self.assertFalse(row['trusted'])
        self.assertIn('selected_fields',row)
    def test_oversized_no_read_no_parse(self):
        with self.file.open('wb') as f:f.truncate(diag.FILE_LIMIT+1)
        with patch.object(diag.json,'loads',side_effect=AssertionError('parse forbidden')):
            row=self.row()
        self.assertIn('bounds denial',row['error']);self.assertIn('hash_unavailable',row);self.assertNotIn('sha256',row)
    def test_exact2MiB_report_full_hash_and_parse(self):
        raw=b'{"decision":{"allowed":false,"reason":"boundary"}}'.ljust(diag.FILE_LIMIT,b' ')
        self.raw(raw);row=self.row()
        self.assertEqual(row['size'],diag.FILE_LIMIT);self.assertEqual(row['sha256'],hashlib.sha256(raw).hexdigest())
        self.assertEqual(row['selected_fields']['decision']['value']['reason'],'boundary')
    def test_nested_selected_combined_budget(self):
        self.raw(json.dumps(dict(decision={'reasons':['X'*70000]},errors=['Y'*70000],reason='small',schema='fixture')).encode())
        row=self.row();fields=row['selected_fields']
        self.assertLessEqual(len(json.dumps(fields).encode()),65536)
        self.assertIn('truncation_error',fields['decision']);self.assertNotIn('value',fields['decision'])
        self.assertIn('truncation_error',fields['errors']);self.assertEqual(fields['reason']['value'],'small')
    def test_strict_parse_errors_retained_with_raw_hash(self):
        for raw in (b'{"decision":1,"decision":2}',b'{"raw_receipts":{"x":1,"x":2}}',b'{"x":NaN}',b'{"x":1e999}',b'{"x":'+b'9'*5000+b'}',b'[]',b'{"x":',b'\xff'):
            self.raw(raw);row=self.row();self.assertIn('parse_error',row);self.assertIn('sha256',row);self.assertNotIn('selected_fields',row)
    def test_whole_interval_drift_owner_partial_read_denial_closes(self):
        for fault in ('fd-drift','entry-drift','owner','partial'):
            r=self.observe(fault);self.assertFalse(r['interval_stable'],fault)
            self.assertTrue(all('sha256' not in row and 'selected_fields' not in row for row in r['files'].values()))
        self.assertIn('error',self.row(fault='read-error'))
    def test_missing_report_and_alias(self):
        p=self.packet/'absent';p.mkdir(mode=0o700);self.parts=(*self.parts,'absent')
        self.assertIn('error',self.row())
        self.assertFalse(self.observe('alias')['interval_stable'])
    def test_worldwrite_denied(self):
        os.chmod(self.file,0o602);self.assertIn('error',self.row())
    def test_alarm_closes_fds(self):
        with patch.object(diag.os,'read',side_effect=TimeoutError('fixture alarm')):
            r=self.observe()
        self.assertFalse(r['interval_stable']);self.assertTrue(r['errors'])
    def test_link_worldwrite_symlink_denials(self):
        os.link(self.file,self.packet/'alias');self.assertIn('error',self.row())
        # New fixture trees remain retained, including this hardlink.
        p=self.packet/'other';p.mkdir(mode=0o700);os.symlink('../'+diag.NAMES[0],p/diag.NAMES[0]);self.parts=(*self.parts,'other')
        self.assertIn('error',self.row())
    def test_new_transport_mock_exact_payload_durable_charge(self):
        capture=self.root/'mock-future-capture';streams=[];calls=[]
        def popen(argv,**kwargs):
            calls.append(argv);self.assertEqual(argv,t.ARGV)
            charge=json.loads((capture/'exclusive-future-charge.json').read_bytes())
            self.assertEqual(charge['SSH_charge'],1);self.assertEqual(charge['payload'],t.PIN)
            self.assertEqual(os.read(kwargs['stdin'],t.LIMIT),t.PAYLOAD.read_bytes())
            for data in (b'fixture diagnostic',b''):
                r,w=os.pipe();os.write(w,data);os.close(w);streams.append(os.fdopen(r,'rb'))
            return SimpleNamespace(pid=987654321,stdout=streams[0],stderr=streams[1],returncode=None,kill=lambda:None)
        usage=resource.getrusage(resource.RUSAGE_SELF)
        with patch.object(t,'CAPTURE',capture),patch.object(t.sys,'argv',['mock-source']),patch.object(t.subprocess,'Popen',popen),patch.object(t.subprocess,'run',return_value=subprocess.CompletedProcess([],0,b'1000\n',b'')),patch.object(t.os,'wait4',return_value=(987654321,0,usage)):
            self.assertEqual(t._reviewed_future(),0)
            self.assertEqual(t._reviewed_future(),78) # exclusive, spent mock capture
        self.assertEqual(len(calls),1);self.assertTrue(all(x.closed for x in streams))
        self.assertTrue(all(stat.S_IMODE(p.stat().st_mode)==0o600 for p in capture.iterdir()))
    def test_exact_payload_pin_argv_disabled_main_fresh_capture(self):
        source=(D/'FinalNativeGate-admission-report.py').read_bytes()
        active=source.replace(b"if __name__=='__main__':raise SystemExit(main())",b"if __name__=='__main__':raise SystemExit(diagnostic_entry())")
        self.assertEqual(active,t.PAYLOAD.read_bytes());self.assertEqual(t.PIN,dict(size=len(active),sha256=hashlib.sha256(active).hexdigest()))
        self.assertEqual(t.ARGV,['/usr/bin/ssh','-T','-oBatchMode=yes','-oConnectTimeout=10','-oStrictHostKeyChecking=yes','-oClearAllForwardings=yes','-oForwardAgent=no','dombarker@100.108.41.90','/usr/bin/python3 -I -B -'])
        self.assertEqual(str(t.CAPTURE),'/private/tmp/FinalNativeGate-admission-report-012-future');self.assertFalse(t.CAPTURE.exists())
        with patch.object(t.subprocess,'Popen',side_effect=AssertionError('SSH forbidden')):
            self.assertEqual(t.main(),78);self.assertEqual(diag.main(),78)
        ast.parse(active)
if __name__=='__main__':unittest.main(verbosity=2)
