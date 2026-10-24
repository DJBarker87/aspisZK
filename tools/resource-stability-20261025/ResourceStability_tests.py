"""New focused tests only; immutable historical suites are not rerun."""
import ast
import copy
import unittest
from ResourceStability_sources import c, go, fixtures, blob, AVAILABLE
import ResourceStability_evaluator as policy

f = fixtures()
G = c.GIB
NUMERIC = ('projected_reserved_bytes', 'min_mem_available_bytes',
           'max_active_file_bytes', 'max_kernel_withheld_bytes',
           'max_root_residual_bytes', 'adjusted_available_bytes', 'required_bytes',
           'margin_bytes', 'cap_ok', 'available_ok', 'legacy_nonreserve_gate_ok', 'allowed')


def sample(ancestor=False):
    s, expected = f['scope'](3*G, 4*G, ancestor)
    root = s['rows'][0]['path']
    other = f['node'](root+'/other', cap=2*G, owner=root)
    other.update(procs=[99], threads=[99,100],
                 identities=[dict(tid=i,tgid=99,starttime=7) for i in (99,100)],
                 pids_enabled=True, tasks_max=64, pids_current=2)
    s['rows'].append(other)
    return s, expected


def counts(s):
    for r in s['rows']:
        if r['pids_enabled']:
            r['pids_current'] = sum(len(x['threads']) for x in s['rows']
                if x['path']==r['path'] or x['path'].startswith(r['path']+'/'))


def result(s, after=None, q=4*G, old=None, **kw):
    return policy.evaluate(f['legacy'](s,q) if old is None else old,
        s, s if after is None else after, q, phase=kw.pop('phase','prospective'), **kw)


def add_task(s, tid, tgid):
    r=s['rows'][-1]
    r['threads'].append(tid)
    r['identities'].append(dict(tid=tid,tgid=tgid,starttime=8))
    if tid==tgid:r['procs'].append(tid)
    counts(s)


class ResourceStabilityTests(unittest.TestCase):
    def denied(self, d):
        self.assertFalse(d['allowed'], {k:v for k,v in d.items() if k not in ('legacy','before_observation','after_observation')})

    def test_unrelated_exit_birth_noninterference(self):
        s,_=sample(); base=result(s)
        self.assertTrue(base['allowed'])
        for kind in ('thread_exit','thread_birth','process_birth','process_exit','reuse'):
            a=copy.deepcopy(s);r=a['rows'][-1]
            if kind=='thread_exit':
                r['threads'].remove(100);r['identities'].pop()
            elif kind=='process_exit':
                r.update(procs=[],threads=[],identities=[])
            elif kind=='reuse':
                for i in r['identities']:i['starttime']+=1
            else:add_task(a,101,99 if kind=='thread_birth' else 101)
            counts(a)
            for before,after in ((s,a),(a,s)):
                d=result(before,after)
                self.assertEqual({k:d[k] for k in NUMERIC},{k:base[k] for k in NUMERIC},kind)
                self.assertEqual(d['before_observation']['bounded_reserved_bytes'],6*G)
                self.assertEqual(d['after_observation']['bounded_reserved_bytes'],6*G)
                self.assertEqual(d['before_observation']['root_residual_bytes'],d['after_observation']['root_residual_bytes'])
                self.assertTrue(d['membership_differences'])
                old=go.evaluate(f['legacy'](before,4*G),before,after,4*G,phase='prospective')
                self.denied(old)
                self.assertEqual(old['error'],'ValueError: hierarchy/membership/control race')
        # Root membership also cannot create numeric credit; collector stays in scope.
        a=copy.deepcopy(s);r=a['rows'][0]
        r.update(procs=[101],threads=[101],identities=[dict(tid=101,tgid=101,starttime=8)])
        d=result(s,a)
        self.assertEqual({k:d[k] for k in NUMERIC},{k:base[k] for k in NUMERIC})

    def test_collector_required_present_stable(self):
        s,_=sample();old=f['legacy'](s,4*G)
        for mode in ('missing_self','exit','starttime','pid','group','path','unified','coherent_reuse','coherent_move'):
            a=copy.deepcopy(s);r=a['rows'][1];i=a['self_observation']
            if mode=='missing_self':del a['self_observation']
            elif mode=='exit':r.update(procs=[],threads=[],identities=[]);counts(a)
            elif mode in ('starttime','pid'):i[mode]+=1
            elif mode=='group':r['identities'][0]['tgid']=99
            elif mode=='path':i['path']='/sys/fs/cgroup/other'
            elif mode=='unified':i['unified_path']='/other'
            elif mode=='coherent_reuse':i['starttime']+=1;r['identities'][0]['starttime']+=1
            else:
                target=a['rows'][-1]
                target['procs'].insert(0,42);target['threads'].insert(0,42)
                target['identities'].insert(0,r['identities'][0])
                r.update(procs=[],threads=[],identities=[])
                i.update(path=target['path'],unified_path='/other');counts(a)
            with self.subTest(mode=mode):self.denied(result(s,a,old=old))
        self.denied(result(s,dict(s,self_observation=dict(s['self_observation'],pid=True))))

    def test_all_structural_controls_race(self):
        s,_=sample()
        changes={'root':True,'parent':'/bad','owner':'/bad','enabled':False,
            'subtree_memory':True,'populated':False,'cap':3*G,'high':2*G,
            'swap_max':G,'tasks_max':63,'pids_enabled':False,'subtree_pids':True,
            'type':'domain threaded','domain':'/bad','procs_errno':95,
            'controllers':['pids','memory']}
        for key,value in changes.items():
            a=copy.deepcopy(s);a['rows'][-1][key]=value
            with self.subTest(key=key):self.denied(result(s,a))
        for mode in ('topology','order','root_control','delegation','population_empty'):
            a=copy.deepcopy(s)
            if mode=='topology':a['rows'].pop()
            elif mode=='order':a['rows'][1:]=reversed(a['rows'][1:])
            elif mode=='root_control':a['rows'][0]['tasks_max']=64
            elif mode=='delegation':a['rows'][0]['controllers']=['memory']
            else:
                a['rows'][-1].update(procs=[],threads=[],identities=[],pids_current=0,populated=False)
            with self.subTest(mode=mode):self.denied(result(s,a))
        # Even a completely valid topology addition and controls change denies.
        a=copy.deepcopy(s)
        extra=f['node']('/sys/fs/cgroup/new',current=0,cap=G,owner='/sys/fs/cgroup')
        extra.update(pids_enabled=True,pids_current=0,tasks_max=64)
        a['rows'].append(extra);c.observe(a)
        self.denied(result(s,a))

    def test_internal_membership_and_receipt_failures(self):
        s,_=sample();old=f['legacy'](s,4*G)
        for mode in ('missing_ids','missing_threads','missing_procs','bad_count','duplicate',
                     'negative_id','invalid_start','missing_start','bad_type','no_status'):
            a=copy.deepcopy(s);r=a['rows'][-1]
            if mode=='missing_ids':r['identities'].pop()
            elif mode=='missing_threads':r['threads'].pop()
            elif mode=='missing_procs':r['procs']=[]
            elif mode=='bad_count':r['pids_current']-=1
            elif mode=='duplicate':r['threads'].append(100)
            elif mode=='negative_id':r['threads'][0]=-1
            elif mode=='invalid_start':r['identities'][0]['starttime']=-1
            elif mode=='missing_start':del r['identities'][0]['starttime']
            elif mode=='bad_type':r['type']='unknown'
            else:del r['identities'][0]['tgid']
            for b,a2 in ((s,a),(a,s)):
                with self.subTest(mode=mode):self.denied(result(b,a2,old=old))
        for field in ('read_attempts','self_read_attempts'):
            for errno in (2,13):
                a=copy.deepcopy(s)
                a[field]=[dict(path='/proc/99/stat',errno=errno,error='captured failure')]
                self.denied(result(s,a))
            a=copy.deepcopy(s)
            a[field]=[dict(path='/proc/99/stat',errno=0,content='bad',sha256='bad')]
            self.denied(result(s,a))
        a=copy.deepcopy(s);del a['rows'][-1]['pids_current'];self.denied(result(s,a))

    def test_inside_scope_unit_ancestors_count_once(self):
        for ancestor in (False,True):
            s,e=sample(ancestor);counts(s)
            kw=dict(q=0,phase='inside-scope',expected=e,expected_unit='job.scope')
            d=result(s,**kw);self.assertTrue(d['allowed'],d.get('error'))
            self.assertEqual(d['projected_reserved_bytes'],(14 if ancestor else 6)*G)
            a=copy.deepcopy(s);add_task(a,101,99)
            self.assertTrue(result(s,a,**kw)['allowed'])
            for unit in (None,'other.scope','../job.scope','job.service'):
                self.denied(result(s,**dict(kw,expected_unit=unit)))
            for key,value in (('high',2*G),('cap',3*G),('tasks_max',63),('swap_max',G),('swap_current',1)):
                a=copy.deepcopy(s);a['rows'][-2][key]=value
                self.denied(result(s,a,**kw))
            if ancestor:
                for key in ('high','cap','tasks_max'):
                    a=copy.deepcopy(s);a['rows'][1][key]=1
                    self.denied(result(s,a,**kw))

    def test_strict_numerical_bounds_unchanged(self):
        s,_=sample()
        for cap in (51*G,51*G-1):
            a=copy.deepcopy(s);a['rows'][1]['cap']=cap-2*G
            d=result(a)
            self.assertEqual(d['cap_ok'],cap<51*G)
            self.assertEqual(d['allowed'],cap<51*G)
        baseline=result(s);adjust=baseline['adjusted_available_bytes'];required=baseline['required_bytes']
        for delta in (0,1):
            a=copy.deepcopy(s);a['meminfo']['MemAvailable']-=adjust-required-delta
            d=result(a)
            self.assertEqual(d['margin_bytes'],delta);self.assertEqual(d['allowed'],delta==1)
        for m in (6*G,6*G+1):
            a=copy.deepcopy(s);a['meminfo']['MemAvailable']=m
            d=result(a);self.assertEqual(d['available_ok'],m>6*G);self.denied(d)
        for value in (-1,True,1.0,c.U64+1):self.denied(result(s,q=value,old=f['legacy'](s,4*G)))
        self.denied(result(s,q=c.U64,old=f['legacy'](s,4*G)))
        for field,value in (('MemAvailable',0),('MemFree',100*G),('KReclaimable',0),('Active(file)',c.U64)):
            a=copy.deepcopy(s);a['meminfo'][field]=value;self.denied(result(s,a))
        for key in ('current','swap_current'):
            a=copy.deepcopy(s);a['rows'][-1][key]=c.U64;self.denied(result(s,a))
        for val in (-1,None,c.U64+1):
            a=copy.deepcopy(s);a['rows'][-1]['stat']['anon']=val;self.denied(result(s,a))

    def test_legacy_and_phase_errors_preserved(self):
        s,e=sample();old=f['legacy'](s,4*G)
        for key in tuple(old)+('error','visibility_error'):
            bad=copy.deepcopy(old)
            if key in old:del bad[key]
            else:bad[key]='captured error'
            self.denied(result(s,old=bad))
        self.denied(result(s,old=dict(old,allowed=False,reserve_check=True)))
        self.denied(result(s,expected_unit='job.scope'))
        for phase,q in (('other',4*G),('prospective',0),('inside-scope',4*G)):
            self.denied(result(s,phase=phase,q=q,old=old))

    def test_source_noninterference_and_numerical_suffix(self):
        # Full numerical/legacy gate suffix is AST-identical to pinned source.
        original=ast.parse(blob('tools/resource-available-20261024/ResourceAvailable_go.py',AVAILABLE))
        from pathlib import Path
        changed=ast.parse(Path(policy.__file__).read_text())
        def suffix(tree):
            fun=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='evaluate')
            body=next(n for n in fun.body if isinstance(n,ast.Try)).body
            start=next(i for i,n in enumerate(body) if isinstance(n,ast.Assign) and isinstance(n.targets[0],ast.Name) and n.targets[0].id=='old_frontier')
            return [ast.dump(n,include_attributes=False) for n in body[start:]]
        self.assertEqual(suffix(original),suffix(changed))
        # observe's membership-derived outputs are diagnostics only. Numeric field
        # selection is additionally reviewed in the audit packet, not a theorem.
        self.assertIs(policy.observe,c.observe);self.assertIs(policy.bind_scope,go.bind_scope)
        self.assertEqual(go.membership,c.membership)
        self.assertRaises(RuntimeError,policy.read_only_admission,phase='prospective',additional_bytes=G)


def run():
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(ResourceStabilityTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():raise AssertionError('ResourceStability focused tests failed')
    return dict(groups=result.testsRun,status='PASS',synthetic=True)


if __name__=='__main__':run()
