import copy
import unittest
from resource_slab_candidate import GIB, LIMIT, U64, accounting, propose, pairs


def node(path, current, *, cap=None, populated=True, slab=0, inactive=0,
         active=0, anon=0, kernel=None, enabled=True, subtree=False, owner='/cg'):
    return dict(path=path, parent=path.rsplit('/', 1)[0], root=False, enabled=enabled,
                owner=owner, subtree_memory=subtree, populated=populated, procs=[],
                current=current, cap=cap, high=None, swap_max=0, swap_current=0,
                tasks_max=None, pids_enabled=False, subtree_pids=False, pids_current=None,
                type='domain', domain=path, threads=[], identities=[], procs_errno=0, controllers=[], stat=dict(inactive_file=inactive, active_file=active,
                    slab_reclaimable=slab, slab_unreclaimable=0, anon=anon,
                    kernel=slab if kernel is None else kernel))


def fixture(*nodes):
    root = dict(path='/cg', parent=None, root=True, enabled=False, owner='/cg',
                subtree_memory=True, procs=[], type='root-special-domain', domain='/cg',
                threads=[], identities=[], procs_errno=0, controllers=['memory'],
                pids_enabled=False, subtree_pids=False, tasks_max=None, pids_current=None)
    top = sum(r['current'] for r in nodes if r['enabled'] and r['owner'] == '/cg')
    return dict(rows=[root, *nodes], meminfo=dict(MemTotal=100*GIB,
                MemFree=100*GIB-top-GIB, MemAvailable=80*GIB))


def legacy(s, requested=4*GIB):
    a = accounting(s)
    return dict(cgroups=[dict(path=p, charged_bytes=next(r['cap'] for r in s['rows'] if r['path']==p)) for p in a['frontier']],
                projected_reserved_bytes=a['bounded_reserved_bytes']+requested,
                allowed=True, reserve_check=True, process_visibility='processes',
                service_visibility='services', docker_visibility=[])


class CandidateTests(unittest.TestCase):
    def proposal(self, s, requested=4*GIB, old=None, after=None):
        return propose(old if old is not None else legacy(s, requested), s,
                       after if after is not None else copy.deepcopy(s), requested)

    def test_finite_ancestor_once(self):
        s=fixture(node('/cg/a', 3*GIB, cap=8*GIB, subtree=True),
                  node('/cg/a/b', GIB, cap=4*GIB, owner='/cg/a'))
        a=accounting(s)
        self.assertEqual(a['bounded_reserved_bytes'], 8*GIB)
        self.assertEqual([r['covered_by'] for r in a['exclusive']], ['/cg/a']*2)
        self.assertEqual(a['uncovered_reserve_bytes'], 0)

    def test_sibling_caps_and_ancestor_constraints(self):
        s=fixture(node('/cg/a', GIB, cap=30*GIB),node('/cg/b', GIB, cap=21*GIB))
        self.assertFalse(self.proposal(s)['allowed'])  # 51+4 ==55, strict
        s['rows'][1]['cap']=29*GIB
        self.assertTrue(self.proposal(s)['allowed'])

    def test_parent_current_inconsistent(self):
        s=fixture(node('/cg/a', 10, subtree=True), node('/cg/a/b', 11, owner='/cg/a'))
        self.assertRaises(ValueError, accounting, s)

    def test_exclusive_accounting_and_nonoverlap(self):
        s=fixture(node('/cg/a', 100, slab=40, inactive=20, subtree=True),
                  node('/cg/a/b', 60, slab=20, inactive=10, owner='/cg/a'))
        a=accounting(s)
        self.assertEqual(sum(d['exclusive_current'] for d in a['exclusive']),100)
        self.assertEqual(a['half_slab_credit_bytes'],20)
        self.assertEqual(a['inactive_file_credit_bytes'],20)
        self.assertEqual(a['uncovered_reserve_bytes'],60)

    def test_empty_charged_finite_and_uncapped(self):
        s=fixture(node('/cg/a', 100, cap=1000, populated=False, anon=100),
                  node('/cg/b', 100, populated=False, kernel=100))
        a=accounting(s)
        self.assertEqual(a['bounded_reserved_bytes'],0)
        self.assertEqual(a['uncovered_reserve_bytes'],200)
        self.assertEqual(self.proposal(s)['coverage_added'],['/cg/a','/cg/b'])

    def test_root_residual_fully_retained(self):
        s=fixture(node('/cg/a',100,slab=100))
        s['rows'][0]['procs']=[2,1234]
        s['rows'][0]['threads']=[2,1234]
        s['rows'][0]['identities']=[dict(tid=i,tgid=i,starttime=1) for i in (2,1234)]
        a=accounting(s)
        self.assertEqual(a['root_residual_bytes'], GIB)
        self.assertEqual(a['root_direct_pids'],[2,1234])
        self.assertEqual(a['half_slab_credit_bytes'],50)

    def test_controller_disabled_subtree_covered_at_owner(self):
        s=fixture(node('/cg/a',100,anon=100),
                  node('/cg/a/b',0,enabled=False,owner='/cg/a'))
        a=accounting(s)
        self.assertEqual(a['uncovered_reserve_bytes'],100)
        self.assertEqual(a['disabled_coverage'][0]['owner'],'/cg/a')

    def test_unknown_controller_owner(self):
        s=fixture(node('/cg/a',100),node('/cg/a/b',0,enabled=False,owner='/bad'))
        self.assertRaises(ValueError,accounting,s)

    def test_disabled_cannot_reenable(self):
        s=fixture(node('/cg/a',100),node('/cg/a/b',0,enabled=False,owner='/cg/a',subtree=True))
        self.assertRaises(ValueError,accounting,s)

    def test_no_credit_inside_finite_frontier(self):
        a=accounting(fixture(node('/cg/a',100,cap=1000,slab=80,inactive=20)))
        self.assertEqual(a['half_slab_credit_bytes'],0)
        self.assertEqual(a['inactive_file_credit_bytes'],0)

    def test_active_anon_unreclaimable_retained(self):
        a=accounting(fixture(node('/cg/a',100,active=20,anon=30,kernel=50)))
        self.assertEqual(a['uncovered_reserve_bytes'],100)

    def test_missing_stat_or_slab_denies(self):
        for key in ('stat','slab_reclaimable'):
            s=fixture(node('/cg/a',100)); old=legacy(s)
            if key=='stat': del s['rows'][1]['stat']
            else: del s['rows'][1]['stat'][key]
            self.assertFalse(self.proposal(s,old=old)['allowed'])

    def test_negative_and_overflow(self):
        for bad in (-1,U64+1,True):
            s=fixture(node('/cg/a',100)); old=legacy(s);s['rows'][1]['current']=bad
            self.assertFalse(self.proposal(s,old=old)['allowed'])
        self.assertRaises(ValueError,pairs,'slab_reclaimable -1')
        self.assertRaises(ValueError,pairs,'anon 1\nanon 2')

    def test_components_exceed_current(self):
        for slab,inactive in ((101,0),(60,60)):
            s=fixture(node('/cg/a',100,slab=slab,inactive=inactive))
            self.assertRaises(ValueError,accounting,s)

    def test_cap_overrun(self):
        self.assertRaises(ValueError,accounting,fixture(node('/cg/a',101,cap=100)))

    def test_parent_component_race(self):
        self.assertRaises(ValueError,accounting,fixture(node('/cg/a',100,slab=10,subtree=True),
                         node('/cg/a/b',50,slab=20,owner='/cg/a')))

    def test_population_race(self):
        self.assertRaises(ValueError,accounting,fixture(node('/cg/a',100,populated=False,subtree=True),
                         node('/cg/a/b',50,owner='/cg/a')))

    def test_low_available_strict_boundary(self):
        s=fixture(node('/cg/a',100));s['meminfo']['MemAvailable']=6*GIB
        self.assertFalse(self.proposal(s)['allowed'])
        s['meminfo']['MemAvailable']+=1
        self.assertTrue(self.proposal(s)['allowed'])

    def test_missing_visibility_and_legacy_errors(self):
        s=fixture(node('/cg/a',100))
        for k in ('process_visibility','service_visibility','docker_visibility'):
            old=legacy(s);del old[k]
            self.assertFalse(self.proposal(s,old=old)['allowed'])
        for k in ('process_visibility','service_visibility','docker_visibility','allowed','reserve_check'):
            old=legacy(s);old[k]=None
            self.assertFalse(self.proposal(s,old=old)['allowed'])
        for k in ('error','visibility_error'):
            old=legacy(s);old[k]='failed';old['reserve_check']=False
            self.assertFalse(self.proposal(s,old=old)['allowed'])

    def test_legacy_cap_denial_never_overridden(self):
        s=fixture(node('/cg/a',100));old=legacy(s)
        old['projected_reserved_bytes']=LIMIT;old['allowed']=False;old['reserve_check']=False
        self.assertFalse(self.proposal(s,old=old)['allowed'])

    def test_legacy_reserve_denial_may_change(self):
        s=fixture(node('/cg/a',100));old=legacy(s);old.update(allowed=False,reserve_check=False)
        self.assertTrue(self.proposal(s,old=old)['allowed'])

    def test_membership_and_controls_race(self):
        s=fixture(node('/cg/a',100))
        for key,value in (('cap',1000),('procs',[999]),('subtree_memory',True),('populated',False)):
            after=copy.deepcopy(s);after['rows'][1][key]=value
            self.assertFalse(self.proposal(s,after=after)['allowed'])
        self.assertFalse(propose(legacy(s),s,None,4*GIB)['allowed'])

    def test_envelope_max_usage_min_credit(self):
        s=fixture(node('/cg/a',100,slab=40,inactive=20));after=copy.deepcopy(s)
        after['rows'][1].update(current=120)
        after['rows'][1]['stat'].update(slab_reclaimable=20,kernel=20,inactive_file=10)
        d=self.proposal(s,after=after)
        self.assertTrue(d['allowed'])
        self.assertEqual(d['envelope'][0]['reserve'],100)

    def test_odd_credit_floor(self):
        self.assertEqual(accounting(fixture(node('/cg/a',5,slab=5)))['half_slab_credit_bytes'],2)

    def test_physical_total_boundary(self):
        s=fixture(node('/cg/a',0));s['meminfo'].update(MemTotal=12*GIB,MemFree=11*GIB,MemAvailable=10*GIB)
        self.assertFalse(self.proposal(s)['allowed']) #4+1+7 ==12

class ScannerTests(unittest.TestCase):
    def test_sysfs_missing_stat_and_slab_and_negative(self):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from unittest.mock import patch
        from resource_slab_candidate import scan
        with TemporaryDirectory() as temp:
            root=Path(temp);child=root/'a';child.mkdir()
            (root/'cgroup.subtree_control').write_text('memory')
            (root/'cgroup.controllers').write_text('memory pids')
            (root/'cgroup.threads').write_text('')
            (root/'cgroup.procs').write_text('')
            files={'cgroup.type':'domain','cgroup.controllers':'memory pids','cgroup.threads':'','pids.current':'0','cgroup.subtree_control':'','cgroup.procs':'', 'cgroup.events':'populated 0\nfrozen 0',
                   'memory.current':'100', 'memory.max':'max','memory.high':'max',
                   'memory.swap.max':'0','memory.swap.current':'0','pids.max':'64',
                   'memory.stat':'inactive_file 0\nactive_file 0\nslab_reclaimable 0\nslab_unreclaimable 0\nanon 100\nkernel 0'}
            for name,value in files.items(): (child/name).write_text(value)
            original=Path.read_text
            def read(path,*args,**kwargs):
                if str(path)=='/proc/meminfo':
                    return 'MemTotal: 100000 kB\nMemFree: 90000 kB\nMemAvailable: 90000 kB\n'
                return original(path,*args,**kwargs)
            with patch.object(Path,'read_text',read):
                a=scan(root); self.assertEqual(accounting(a)['uncovered_reserve_bytes'],100)
                self.assertIn(str(child/'memory.stat'),a['raw_sha256'])
                # A memory-enabled child need not delegate pids. Missing pids.max
                # is legitimate only when the parent does not enable pids.
                (child/'pids.max').unlink()
                self.assertIsNone(scan(root)['rows'][1]['tasks_max'])
                (root/'cgroup.subtree_control').write_text('memory pids')
                self.assertRaises(OSError,scan,root)
                (child/'pids.max').write_text('64')
                self.assertEqual(scan(root)['rows'][1]['tasks_max'],64)
                (child/'memory.stat').unlink()
                self.assertRaises(OSError,scan,root)
                (child/'memory.stat').write_text('anon 100')
                self.assertRaises(KeyError,accounting,scan(root))
                (child/'memory.stat').write_text(files['memory.stat'])
                (child/'memory.current').write_text('-1')
                self.assertRaises(ValueError,scan,root)


class FailureRetentionTests(unittest.TestCase):
    def test_unsupported_read_denies_and_keeps_old_visibility(self):
        from unittest.mock import patch
        import resource_slab_candidate as candidate
        s=fixture(node('/cg/a',100));old=legacy(s)
        with patch.object(candidate,'scan',side_effect=OSError(95,'Operation not supported')):
            out=candidate.live(lambda requested:old,{})
        self.assertEqual(out['original_legacy'],old)
        self.assertIn('Operation not supported',out['collection_error'])
        self.assertTrue(all(not d['allowed'] for d in out['decisions'].values()))
        self.assertIsNone(out['snapshots']['before'])

    def test_unaccountable_global_residual_denies(self):
        s=fixture(node('/cg/a',100))
        s['meminfo']['MemFree']=s['meminfo']['MemTotal']
        self.assertRaises(ValueError,accounting,s)


if __name__=='__main__':
    unittest.main(verbosity=2)

class ThreadedTests(unittest.TestCase):
    def setup_tree(self, temp):
        from pathlib import Path
        root=Path(temp); domain=root/'d'; domain.mkdir(); thread=domain/'t';thread.mkdir()
        data={root:{'cgroup.controllers':'memory pids','cgroup.subtree_control':'memory pids',
                    'cgroup.procs':'','cgroup.threads':''},
              domain:{'cgroup.type':'domain threaded','cgroup.controllers':'memory pids',
                    'cgroup.subtree_control':'pids','cgroup.procs':'42','cgroup.threads':'',
                    'cgroup.events':'populated 1','pids.max':'64','pids.current':'1',
                    'memory.current':'100','memory.max':'max','memory.high':'max',
                    'memory.swap.max':'0','memory.swap.current':'0',
                    'memory.stat':'inactive_file 0\nactive_file 0\nslab_reclaimable 40\nslab_unreclaimable 0\nanon 60\nkernel 40'},
              thread:{'cgroup.type':'threaded','cgroup.controllers':'pids','cgroup.subtree_control':'',
                      'cgroup.threads':'43','cgroup.events':'populated 1','pids.max':'64','pids.current':'1'}}
        for path,files in data.items():
            for name,value in files.items(): (path/name).write_text(value)
        return root,domain,thread

    def run_scan(self, mutate=None, read_mutate=None):
        from pathlib import Path
        from tempfile import TemporaryDirectory
        from unittest.mock import patch
        from resource_slab_candidate import scan
        with TemporaryDirectory() as temp:
            root,domain,thread=self.setup_tree(temp)
            if mutate: mutate(root,domain,thread)
            original=Path.read_text
            def read(path,*args,**kwargs):
                if read_mutate:
                    result=read_mutate(path,root,domain,thread)
                    if result is not None: return result
                if path == thread/'cgroup.procs': raise OSError(95,'threaded unsupported')
                if str(path)=='/proc/meminfo': return 'MemTotal: 100000 kB\nMemFree: 90000 kB\nMemAvailable: 90000 kB\n'
                if str(path)=='/proc/43/stat': return '43 (name with ) space) '+ ' '.join(['S']+['0']*18+['123'])
                if str(path)=='/proc/43/status': return 'Pid:\t43\nTgid:\t42\n'
                if str(path)=='/proc/43/cgroup': return '0::/d/t\n'
                return original(path,*args,**kwargs)
            with patch.object(Path,'read_text',read): return scan(root)

    def test_complete_threaded_alternative_and_actual_tag_capture(self):
        s=self.run_scan();a=accounting(s)
        self.assertEqual(a['uncovered_reserve_bytes'],80)
        self.assertEqual(a['disabled_coverage'][0]['owner'],s['rows'][1]['path'])
        self.assertEqual(s['rows'][2]['domain'],s['rows'][1]['path'])
        self.assertEqual(s['rows'][2]['type'],'threaded')
        self.assertEqual(s['rows'][2]['tasks_max'],64) # pids despite memory disabled
        self.assertEqual(s['rows'][2]['procs_errno'],95)
        self.assertTrue(any(r['errno']==95 for r in s['read_attempts']))
        self.assertTrue(any(r['path'].endswith('/cgroup.type') and r.get('content')=='threaded' for r in s['read_attempts']))

    def test_unknown_eopnotsupp_denies(self):
        def read(path,root,d,t):
            if path==d/'cgroup.procs': raise OSError(95,'domain unsupported')
        self.assertRaises(OSError,self.run_scan,read_mutate=read)

    def test_unknown_and_invalid_tags_deny(self):
        for value in ('domain invalid','domain (invalid)','unknown'):
            self.assertRaises(ValueError,self.run_scan,lambda r,d,t:(t/'cgroup.type').write_text(value))

    def test_missing_domain_or_thread_or_identity_denies(self):
        for name in ('cgroup.threads','pids.max','pids.current'):
            self.assertRaises(OSError,self.run_scan,lambda r,d,t:(t/name).unlink())
        for interface in ('stat','status','cgroup'):
            def read(path,root,d,t):
                if str(path)=='/proc/43/'+interface: raise PermissionError(13,'live unreadable')
            self.assertRaises(OSError,self.run_scan,read_mutate=read)
        self.assertRaises(ValueError,self.run_scan,lambda r,d,t:(d/'cgroup.procs').write_text(''))

    def test_type_transition_denies(self):
        calls=[]
        def read(path,root,d,t):
            if path==t/'cgroup.type':
                calls.append(1);return 'threaded' if len(calls)==1 else 'domain'
        self.assertRaises(ValueError,self.run_scan,read_mutate=read)

    def test_threaded_memory_delegation_denies(self):
        for name in ('cgroup.controllers','cgroup.subtree_control'):
            self.assertRaises(ValueError,self.run_scan,lambda r,d,t:(t/name).write_text('memory pids'))

    def test_wrong_domain_memory_owner_and_membership_deny(self):
        s=self.run_scan()
        for field,value in (('domain',s['rows'][0]['path']),('owner','/unknown'),('enabled',True),('procs_errno',0),('pids_enabled',False)):
            bad=copy.deepcopy(s);bad['rows'][2][field]=value
            self.assertRaises((ValueError,KeyError),accounting,bad)
        for name,value in (('status','Pid: 43\nTgid: 99'),('cgroup','0::/wrong')):
            def read(path,root,d,t):
                if str(path)=='/proc/43/'+name:return value
            self.assertRaises(ValueError,self.run_scan,read_mutate=read)

    def test_thread_exit_or_identity_reuse_denies(self):
        count=[]
        def read(path,root,d,t):
            if str(path)=='/proc/43/stat':
                count.append(1)
                if len(count)>1:raise FileNotFoundError(2,'thread exited')
        self.assertRaises(OSError,self.run_scan,read_mutate=read)
        count.clear()
        def reuse(path,root,d,t):
            if str(path)=='/proc/43/stat':
                count.append(1);return '43 (x) '+' '.join(['S']+['0']*18+[str(len(count))])
        self.assertRaises(ValueError,self.run_scan,read_mutate=reuse)

    def test_pids_current_population_and_duplicates_deny(self):
        for name,value in (('pids.current','0'),('cgroup.events','populated 0'),('cgroup.threads','43\n43')):
            self.assertRaises(ValueError,self.run_scan,lambda r,d,t:(t/name).write_text(value))

    def test_observed_root_type_supported_without_inferred_tag(self):
        s=self.run_scan(lambda r,d,t:(r/'cgroup.type').write_text('domain'))
        self.assertEqual(s['rows'][0]['type'],'domain')
        accounting(s)

    def test_type_and_identity_snapshot_changes_deny(self):
        s=self.run_scan();old=legacy(s)
        for field,value in (('type','domain'),('domain','/bad'),('threads',[]),('controllers',[])):
            after=copy.deepcopy(s);after['rows'][2][field]=value
            self.assertFalse(propose(old,s,after,4*GIB)['allowed'])

class CollectorTests(unittest.TestCase):
    def test_retains_exact_legacy_and_failed_snapshot_reads_without_host(self):
        import ast
        import importlib.util
        import json
        from pathlib import Path
        import subprocess
        from tempfile import TemporaryDirectory
        from unittest.mock import patch
        spec=importlib.util.spec_from_file_location('collector',Path(__file__).with_name('collect_readonly.py'))
        module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module)
        attempts=[dict(path='/cg/cgroup.type',content='threaded',errno=0,sha256='example'),
                  dict(path='/cg/cgroup.procs',errno=95,error='unsupported')]
        report=dict(legacy_read_inputs=attempts,snapshots=dict(before=None,after=None),
                    decisions={'1':dict(allowed=False,error='missing hierarchy')},
                    original_legacy={'allowed':False},partial_raw_inputs=None,
                    failures={'before':dict(error='unreadable',raw_inputs={},read_attempts=attempts)},
                    collection_error='unreadable')
        def transport(command,*,input,**kwargs):
            ast.parse(input) # validate the exact generated remote program
            self.assertEqual(command[-1],'python3 -B -')
            return subprocess.CompletedProcess(command,0,json.dumps(report),'')
        with TemporaryDirectory() as temp, patch.object(module,'OUT',Path(temp)), patch.object(module.subprocess,'run',transport), patch.object(module.subprocess,'check_output',return_value='synthetic-revision'):
            module.main()
            self.assertEqual(json.loads((Path(temp)/'reads-before-0000.json').read_text()),attempts)
            self.assertEqual(json.loads((Path(temp)/'reads-legacy-0000.json').read_text()),attempts)
            self.assertEqual(json.loads((Path(temp)/'live-command.json').read_text())['exit'],0)
