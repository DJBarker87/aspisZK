"""New synthetics only. No host reads/SSH/old suites; real scanner exercised."""
import ast
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import shlex
import subprocess
import sys
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch
import ResourceAdmit_adapter as a
import ResourceAdmit_host as h
import ResourceAdmit_local as local
import ResourceAdmit_audit as audit
from ResourceAdmit_sources import functions,load_bundle,digest

fixtures=functions(load_bundle()['fixtures']['source'],['node','fixture','scope'],dict(c=a.c,G=a.c.GIB))

def fixture(ancestor=False):
    s,_=fixtures['scope'](3*a.c.GIB,4*a.c.GIB,ancestor)
    pid=os.getpid();row=s['rows'][-1]
    old=row['path'];new=str(Path(old).with_name(a.UNIT+'.scope'))
    row.update(path=new,domain=new,procs=[pid],threads=[pid],identities=[dict(tid=pid,tgid=pid,starttime=123)])
    s['self_observation'].update(pid=pid,path=new,unified_path=new[len('/sys/fs/cgroup'):])
    return s

def virtual(s):
    """Exact synthetic kernel interfaces, not a supplied live identity."""
    files={};directories={}
    files['/proc/meminfo']=''.join(f'{k}: {v//1024} kB\n' for k,v in s['meminfo'].items())
    for row in s['rows']:
        p=row['path'];directories[p]=[c['path'] for c in s['rows'] if c['parent']==p]
        vals={'cgroup.subtree_control':' '.join(x for x,flag in [('memory',row['subtree_memory']),('pids',row['subtree_pids'])] if flag),
              'cgroup.controllers':' '.join(row['controllers']),'cgroup.threads':' '.join(map(str,row['threads'])),
              'cgroup.procs':' '.join(map(str,row['procs']))}
        if not row['root']:vals.update({'cgroup.type':row['type'],'cgroup.events':f"populated {int(row['populated'])}\nfrozen 0"})
        if row['pids_enabled']:vals.update({'pids.max':row['tasks_max'],'pids.current':row['pids_current']})
        if row['enabled']:
            for field,name in [('current','memory.current'),('cap','memory.max'),('high','memory.high'),('swap_max','memory.swap.max'),('swap_current','memory.swap.current')]:vals[name]='max' if row[field] is None else row[field]
            vals['memory.stat']=''.join(f'{k} {v}\n' for k,v in row['stat'].items())
        for name,val in vals.items():files[p+'/'+name]=str(val).rstrip('\n')+'\n'
        for i in row['identities']:
            prefix='/proc/'+str(i['tid']);pid=i['tid']
            files[prefix+'/stat']=f'{pid} (ResourceAdmit synthetic) '+' '.join(['S']+['0']*18+[str(i['starttime'])])+'\n'
            files[prefix+'/status']=f"Pid: {pid}\nTgid: {i['tgid']}\n"
            files[prefix+'/cgroup']='0::'+p[len('/sys/fs/cgroup'):]+'\n'
    own=s['self_observation']['pid']
    for name in ('stat','status','cgroup'):files['/proc/self/'+name]=files[f'/proc/{own}/'+name]
    def read(path,*args,**kwargs):
        path=str(path)
        if path not in files:raise FileNotFoundError(2,'synthetic absent',path)
        value=files[path]
        if isinstance(value,Exception):raise value
        return value
    @contextlib.contextmanager
    def scandir(path):
        yield [SimpleNamespace(path=x,name=Path(x).name,is_dir=lambda **kw:True) for x in directories[str(path)]]
    def run(argv,*args,**kwargs):
        if argv==a.COMMANDS[0]:output=f'PID PPID RSS COMMAND CGROUP\n{own} 1 100 python {s["self_observation"]["unified_path"]}\n'
        elif argv==a.COMMANDS[1]:output='example.service loaded active running example\n'
        elif argv==a.COMMANDS[2]:output=''
        else:raise AssertionError(('unexpected command',argv))
        return subprocess.CompletedProcess(argv,0,output,'')
    return files,read,scandir,run

@contextlib.contextmanager
def kernel(s):
    files,read,scandir,run=virtual(s)
    with patch.object(Path,'read_text',read),patch.object(os,'scandir',scandir),patch.object(subprocess,'run',run):yield files

class ResourceAdmitTests(unittest.TestCase):
    def test_syntax_and_scope_argv(self):
        for p in Path(__file__).parent.glob('ResourceAdmit_*.py'):ast.parse(p.read_text())
        argv=h.scope_argv()
        self.assertEqual(argv[:12],['systemd-run','--user','--scope','--unit='+a.UNIT,'-p','MemoryHigh=3G','-p','MemoryMax=4G','-p','MemorySwapMax=0','-p','TasksMax=64'])
        self.assertEqual(argv[-1],'go')

    def test_denials_prevent_scope_and_marker(self):
        self.assertFalse(h.flow(lambda:{'decision':{'allowed':False}},lambda:self.fail('scope'))['scope_created'])
        self.assertIsNone(h.go_flow({'decision':{'allowed':False}},lambda:self.fail('marker'))['marker_exit'])
        marked=[];h.go_flow({'decision':{'allowed':True}},lambda:marked.append(1));self.assertEqual(marked,[1])

    def test_real_api_synthetic_proc_count_once_and_ancestor(self):
        for ancestor in (False,True):
            s=fixture(ancestor)
            with kernel(s):report=a.read_only_admission(phase='inside-scope')
            d=report['decision'];self.assertTrue(d['allowed'],d)
            self.assertEqual(d['additional_bytes'],0)
            self.assertEqual(d['projected_reserved_bytes'],(12 if ancestor else 4)*a.c.GIB)
            self.assertEqual(d['scope_binding']['self_identity']['pid'],os.getpid())
        with self.assertRaises(TypeError):a.read_only_admission(phase='inside-scope',pid=42)
        with self.assertRaises(TypeError):a.read_only_admission(phase='inside-scope',path='/fake.scope')

    def test_prospective_fixed_four_and_disabled_old_boundary(self):
        with kernel(fixture()):r=a.read_only_admission(phase='prospective')
        self.assertTrue(r['decision']['allowed'],r['decision'])
        self.assertEqual(r['decision']['additional_bytes'],4*a.c.GIB)
        with self.assertRaises(RuntimeError):a.go['read_only_admission'](phase='prospective',additional_bytes=4*a.c.GIB)

    def test_proc_fakes_and_unit_denied(self):
        for key,value in [('/proc/self/stat','42 (fake) '+' '.join(['S']+['0']*18+['123'])),('/proc/self/cgroup','0::/fake.scope\n'),('/proc/self/status','Pid: 1\nTgid: 1\n')]:
            with kernel(fixture()) as files:
                files[key]=value;r=a.read_only_admission(phase='inside-scope')
            self.assertFalse(r['decision']['allowed'],key)
        s=fixture();old=s['rows'][-1]['path'];s['rows'][-1].update(path=old.replace(a.UNIT,'other'),domain=old.replace(a.UNIT,'other'))
        s['self_observation'].update(path=old.replace(a.UNIT,'other'),unified_path=s['self_observation']['unified_path'].replace(a.UNIT,'other'))
        with kernel(s):r=a.read_only_admission(phase='inside-scope')
        self.assertFalse(r['decision']['allowed'])

    def test_raw_missing_controls_errors_ancestors(self):
        for name in ('memory.max','memory.high','memory.swap.max','pids.max','memory.stat','cgroup.controllers','cgroup.threads'):
            with kernel(fixture()) as files:
                files['/sys/fs/cgroup/'+a.UNIT+'.scope/'+name]=PermissionError(13,'synthetic denied')
                r=a.read_only_admission(phase='inside-scope')
            self.assertFalse(r['decision']['allowed'],name)
        for key,value in [('cap',8*a.c.GIB),('high',4*a.c.GIB),('swap_max',1),('tasks_max',65),('swap_current',1)]:
            s=fixture();s['rows'][-1][key]=value
            with kernel(s):r=a.read_only_admission(phase='inside-scope')
            self.assertFalse(r['decision']['allowed'],key)
        for key in ('cap','high','tasks_max'):
            s=fixture(True);s['rows'][1][key]=1
            with kernel(s):r=a.read_only_admission(phase='inside-scope')
            self.assertFalse(r['decision']['allowed'],key)

    def test_control_and_identity_race(self):
        s=fixture();later=copy.deepcopy(s);later['rows'][-1]['high']+=1
        old=a.visibility
        with kernel(s):visible=old(0)
        with patch.object(a,'visibility',return_value=visible),patch.dict(a.identity,scan_bound=unittest.mock.Mock(side_effect=[s,later])):
            self.assertFalse(a.read_only_admission(phase='inside-scope')['decision']['allowed'])

    def test_visibility_all_errors_deny(self):
        for exc in (PermissionError(13,'denied'),subprocess.CalledProcessError(1,['systemctl']),subprocess.TimeoutExpired(['docker'],15)):
            with kernel(fixture()),patch.object(subprocess,'run',side_effect=exc):r=a.read_only_admission(phase='prospective')
            self.assertFalse(r['decision']['allowed']);self.assertIn('visibility',r['decision']['collection_failures'])

    def test_source_env_runtime_drift(self):
        with tempfile.TemporaryDirectory() as t,patch.object(h,'HERE',Path(t)):
            p=Path(t)/'x';p.write_text('old');pins=dict(files={'x':h.filepin(p)},runtime={},env={},mode=h.MODE)
            p.write_text('new')
            with self.assertRaisesRegex(ValueError,'source drift'):h.verify(pins)
            p.unlink()
            with self.assertRaises(FileNotFoundError):h.verify(pins)
        pins=dict(files={},runtime={'old':1},env={},mode=h.MODE)
        with patch.object(h,'runtime_pins',return_value={}):
            with self.assertRaisesRegex(ValueError,'runtime/dependency drift'):h.verify(pins)
            pins['runtime']={}
            with self.assertRaisesRegex(ValueError,'environment'):h.verify(pins)

    def test_malformed_visibility_and_mode_pin(self):
        for target,output in [(a.COMMANDS[0],'malformed'),(a.COMMANDS[1],'malformed'),(a.COMMANDS[2],'not-a-container')]:
            _,_,_,run=virtual(fixture())
            def malformed(argv,*args,**kwargs):
                return subprocess.CompletedProcess(argv,0,output,'') if argv==target else run(argv,*args,**kwargs)
            with kernel(fixture()),patch.object(subprocess,'run',malformed):r=a.read_only_admission(phase='prospective')
            self.assertFalse(r['decision']['allowed'])
        with self.assertRaisesRegex(ValueError,'mode pin drift'):h.verify(dict(mode='other'))

    def test_ordered_full_new_trace_replay_hash_and_tamper(self):
        for phase in ('prospective','inside-scope'):
            with tempfile.TemporaryDirectory() as t,patch.object(h,'HERE',Path(t)),patch.object(audit,'OUT',Path(t)):
                with kernel(fixture()):r=h.collect(phase)
                self.assertTrue(r['decision']['allowed'],r['decision'])
                cap=Path(t)/'capture';pins={p.name:dict(name=p.name,**h.filepin(p)) for p in cap.iterdir()}
                (cap/'export-receipt.json').write_text(json.dumps(dict(host_files=pins)))
                with patch.object(audit,'OUT',cap):self.assertTrue(audit.replay(phase)['allowed'])
                events=json.loads((cap/(phase+'-ordered.json')).read_text());events[0]['path']='/fake'
                (cap/(phase+'-ordered.json')).write_text(json.dumps(events))
                with patch.object(audit,'OUT',cap),self.assertRaises(AssertionError):audit.replay(phase)

    def test_scope_peak_swap_pressure_and_missing_controls(self):
        values={'memory.high':str(h.EXPECTED['high']),'memory.max':str(h.EXPECTED['cap']),
                'memory.swap.max':'0','memory.swap.current':'0','pids.max':'64',
                'pids.current':'1','memory.current':'100','memory.peak':'200',
                'memory.events':'low 0\nhigh 0\nmax 0\noom 0\noom_kill 0\noom_group_kill 0\n'}
        self.assertTrue(h.check_controls(dict(values=values)))
        for name in values:
            bad=dict(values);del bad[name]
            with self.assertRaises((KeyError,TypeError,ValueError)):h.check_controls(dict(values=bad))
        for name,value in [('memory.swap.current','1'),('memory.peak',str(5*a.c.GIB)),('memory.events',values['memory.events'].replace('high 0','high 1'))]:
            with self.assertRaises(ValueError):h.check_controls(dict(values=dict(values,**{name:value})))

    def test_denied_raw_and_command_trace_replay(self):
        for fault in ('read','stat','command','scandir'):
            with tempfile.TemporaryDirectory() as t,patch.object(h,'HERE',Path(t)):
                with kernel(fixture()) as files:
                    if fault=='read':files['/proc/self/status']=PermissionError(13,'synthetic denied')
                    if fault=='stat':files['/proc/self/stat']=PermissionError(13,'synthetic stat denied')
                    if fault=='command':
                        with patch.object(subprocess,'run',side_effect=subprocess.CalledProcessError(2,a.COMMANDS[0],output='',stderr='denied')):r=h.collect('prospective')
                    elif fault=='scandir':
                        with patch.object(os,'scandir',side_effect=PermissionError(13,'synthetic scandir denied')):r=h.collect('prospective')
                    else:r=h.collect('prospective')
                self.assertFalse(r['decision']['allowed'])
                cap=Path(t)/'capture';pins={p.name:dict(name=p.name,**h.filepin(p)) for p in cap.iterdir()}
                (cap/'export-receipt.json').write_text(json.dumps(dict(host_files=pins)))
                with patch.object(audit,'OUT',cap):self.assertFalse(audit.replay('prospective')['allowed'])

    def test_transport_failure_charges_once_and_retains_bytes(self):
        with tempfile.TemporaryDirectory() as t,patch.object(local,'OUT',Path(t)),patch.object(local,'coordination',return_value={}),patch.object(local,'revision',return_value='synthetic-source'):
            (Path(t)/'manifest.json').write_text(json.dumps(dict(env=local.env(1000))))
            with patch.object(subprocess,'run',side_effect=subprocess.TimeoutExpired(['ssh'],120,output=b'raw output',stderr=b'raw error')):
                with self.assertRaises(subprocess.TimeoutExpired):local.run()
            self.assertTrue((Path(t)/'ATTEMPTED').exists())
            receipt=json.loads((Path(t)/'run-transport.json').read_text())
            self.assertEqual(receipt['stdout_base64'],'cmF3IG91dHB1dA==')
            with patch.object(subprocess,'run',side_effect=AssertionError('second transport')):
                with self.assertRaises(FileExistsError):local.run()

    def test_coordination_never_reads_live_output(self):
        result=subprocess.CompletedProcess([],0,'7112 '+local.COORD_START+' sh codex-run.sh','')
        with patch.object(subprocess,'run',return_value=result),patch.object(Path,'read_text',side_effect=AssertionError('read live output')):
            with self.assertRaisesRegex(RuntimeError,'WAITING'):local.coordination()

    def test_payload_quotes_and_newline_exact_execution(self):
        def fake(payload,label,environment=None,data=None):
            argv=shlex.split(shlex.join(['env','-i','A=quote\'\n$()`','/usr/bin/python3','-c',payload]))
            self.assertEqual(argv[-1],payload);ast.parse(payload)
            if label=='inspect':return subprocess.CompletedProcess([],0,json.dumps(dict(runtime={},uid=os.getuid(),stage_exists=False,parent_uid=os.getuid(),parent_resolved='/unused',parent_mode='0o755',lock_exists=True)),'')
            self.assertEqual(label,'stage')
            x=json.loads(data)
            with tempfile.TemporaryDirectory() as t:
                root=Path(t).resolve()/'stage';x['manifest']['parent_resolved']=str(root.parent)
                text=payload.replace(repr(local.REMOTE),repr(str(root)))
                with patch.object(sys,'stdin',io.StringIO(json.dumps(x))),contextlib.redirect_stdout(io.StringIO()):exec(text,{})
                raw=(root/'ResourceAdmit_manifest.json').read_bytes()
                self.assertEqual(raw[-1:],b'\n');self.assertEqual(json.loads(raw),x['manifest'])
                self.assertEqual((root/'ResourceAdmit_adapter.py').read_bytes(),local.sources()['ResourceAdmit_adapter.py'].encode())
            return subprocess.CompletedProcess([],0,'{}','')
        with tempfile.TemporaryDirectory() as t,patch.object(local,'OUT',Path(t)),patch.object(local,'ssh_python',fake):
            local.inspect();local.stage()

if __name__=='__main__':unittest.main(verbosity=2)
