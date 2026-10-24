import copy
import unittest
from resource_slab_candidate import GIB, LIMIT, U64, accounting, propose, pairs


def node(path, current, *, cap=None, populated=True, slab=0, inactive=0,
         active=0, anon=0, kernel=None, enabled=True, subtree=False, owner='/cg'):
    return dict(path=path, parent=path.rsplit('/', 1)[0], root=False, enabled=enabled,
                owner=owner, subtree_memory=subtree, populated=populated, procs=[],
                current=current, cap=cap, high=None, swap_max=0, swap_current=0,
                tasks_max=64, stat=dict(inactive_file=inactive, active_file=active,
                    slab_reclaimable=slab, slab_unreclaimable=0, anon=anon,
                    kernel=slab if kernel is None else kernel))


def fixture(*nodes):
    root = dict(path='/cg', parent=None, root=True, enabled=False, owner='/cg',
                subtree_memory=True, procs=[])
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
            (root/'cgroup.procs').write_text('')
            files={'cgroup.subtree_control':'','cgroup.procs':'', 'cgroup.events':'populated 0\nfrozen 0',
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
