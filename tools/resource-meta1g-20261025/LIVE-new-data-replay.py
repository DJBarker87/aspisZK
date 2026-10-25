"""New-data metadata epoch harness. See LIVE-REPLAY-DELTA.md; no live fallback."""
import base64,contextlib,hashlib,importlib.util,json,os,subprocess,sys,time,types,resource
from pathlib import Path
HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
spec=importlib.util.spec_from_file_location('capture',HERE/'LIVE-EVIDENCE-capture.py');capture=importlib.util.module_from_spec(spec);spec.loader.exec_module(capture)
OUT=capture.OUT
import ResourceMeta1G_adapter as adapter
from ResourceMeta1G_sources import bundle,validate_bundle
sources=bundle();validate_bundle(sources)
manifest=json.loads((OUT/'manifest.json').read_text())
expected={k:manifest[k] for k in ('files','runtime','env','mode')}
start=time.monotonic();result={'print_axioms':'N/A','mode':'offline retained actual inputs only','source_revision':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'manifest_revision':manifest['source_revision'],'source_pins':{k:{a:b for a,b in v.items() if a!='source'} for k,v in sources.items()}}
def pin(b):return dict(sha256=hashlib.sha256(b).hexdigest(),size=len(b))
for name,p in manifest['files'].items():
    b=(json.dumps(sources,sort_keys=True,indent=2)+'\n').encode() if name=='ResourceMeta1G_reviewed.json' else (HERE/name).read_bytes()
    assert pin(b)==p,('source pin',name)
for name in ('run-pre-pins.json','run-post-pins.json','go-pre-pins.json','go-pins.json','go-post-pins.json'):
    assert capture.load(name)==expected,('capture pin',name)
for action in ('run','go'):
    for tag in ('initial','final'):
        assert capture.load(action+'-inherited-limits-'+tag+'.json')==manifest['inherited_limits']
result['source_runtime_environment_file_limits_pins']='all retained run/go pre/intermediate/post maps exactly match staged manifest; no fresh host identity check'
result['phases']={}
for phase in ('prospective','inside-scope'):
    raw_report=capture.raw(phase+'-report.json');report=json.loads(raw_report)
    ordered=capture.load(phase+'-ordered.json');pos=0
    for e in ordered:
        if e['kind']=='read' and not e.get('errno'):
            assert pin(e['content'].encode())=={k:e[k] for k in ('sha256','size')}
    def take(kind,**fields):
        global pos
        assert pos<len(ordered),('unexpected replay input',kind,fields,pos)
        e=ordered[pos];pos+=1
        assert e['kind']==kind and all(e[k]==v for k,v in fields.items()),('ordered mismatch',pos,kind,fields,e.get('kind'),e.get('path'))
        return e
    def error(e):
        # Replay Linux errno and its retained raw text, independent of Darwin strerror.
        cls=type('RecordedOSError',(FileNotFoundError if e['errno']==2 else OSError,),{'__str__':lambda self:e['error']})
        exc=cls(e['errno'],e['error'])
        raise exc
    def read(path,*args,**kwargs):
        e=take('read',path=str(path))
        if e.get('errno'):error(e)
        return e['content']
    def run(argv,*args,**kwargs):
        e=take('command',command=argv)
        assert 'error' not in e,('unhandled recorded command exception',e)
        r=subprocess.CompletedProcess(argv,e['exit'],e['stdout'],e['stderr'])
        if kwargs.get('check') and r.returncode:raise subprocess.CalledProcessError(r.returncode,argv,output=r.stdout,stderr=r.stderr)
        return r
    class Entry:
        def __init__(self,e):self.name=e['name'];self.path=e['path'];self.directory=e['is_dir']
        def is_dir(self,*,follow_symlinks):
            assert follow_symlinks is False
            return self.directory
    @contextlib.contextmanager
    def scandir(path):
        e=take('scandir',path=str(path))
        if e.get('errno'):error(e)
        yield iter(Entry(x) for x in e['entries'])
    old=(Path.read_text,subprocess.run,os.scandir,os.getpid)
    try:
        Path.read_text=read;subprocess.run=run;os.scandir=scandir;os.getpid=lambda:report['collector_pid']
        actual=adapter.read_only_admission(phase=phase)
    finally:Path.read_text,subprocess.run,os.scandir,os.getpid=old
    assert pos==len(ordered),('unconsumed ordered inputs',phase,pos,len(ordered))
    assert actual==report,('full collector report mismatch',phase)
    encoded=(json.dumps(actual,sort_keys=True,indent=2)+'\n').encode()
    assert encoded==raw_report,('full serialized report mismatch',phase)
    decision=adapter.policy.evaluate(report['original_legacy'],report['snapshots']['before'],report['snapshots']['after'],adapter.c.GIB if phase=='prospective' else 0,phase=phase,expected=adapter.EXPECTED if phase=='inside-scope' else None,expected_unit=adapter.UNIT+'.scope' if phase=='inside-scope' else None)
    assert decision==report['decision']
    result['phases'][phase]=dict(ordered_events=pos,ordered_pin=pin(capture.raw(phase+'-ordered.json')),report_pin=pin(raw_report),full_ordered_collector_replay='PASS exact full report bytes',evaluator_replay='PASS exact decision',allowed=decision['allowed'],margin_bytes=decision['margin_bytes'],adjusted_available_bytes=decision['adjusted_available_bytes'],required_bytes=decision['required_bytes'],projected_reserved_bytes=decision['projected_reserved_bytes'])
    del raw_report,report,ordered,actual,encoded,decision
# Source-audited control checks, executed from exact pinned function only offline.
import ast
host_source=(HERE/'ResourceMeta1G_host.py').read_text();tree=ast.parse(host_source)
node=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='check_controls')
env=dict(adapter=adapter,EXPECTED=adapter.EXPECTED)
exec(compile(ast.Module(body=[node],type_ignores=[]),'pinned check_controls offline','exec'),env)
controls={}
for name in ('go-controls-before.json','go-controls-after-scan.json','go-controls-after.json'):
    v=capture.load(name);assert env['check_controls'](v)
    controls[name]={k:v['values'][k] for k in ('memory.high','memory.max','memory.peak','memory.swap.current','memory.events','pids.max')}
    identity={k:v for k,v in v['self_observation'].items() if k!='reads'}
    assert identity==capture.load('inside-scope-report.json')['decision']['scope_binding']['self_identity']
result['controls']=controls
assert capture.load('go-control-check.json')==dict(allowed=True)
assert capture.load('scope-argv.json')==capture.load('scope-child.json')['argv']==manifest['scope_argv']
assert capture.load('run-exit.json')['terminal']=='SCOPE_EXIT'
assert capture.load('go-exit.json')['terminal']=='GO_MARKER_PASS'
assert capture.load('scope-child.json')['exit']==capture.load('run-exit.json')['exit']==capture.load('go-exit.json')['exit']==0
assert json.loads((OUT/'LIVE-EVIDENCE-index.json').read_text())['inventory']['marker.json']['status']=='PRESENT'
result['cause']='New epoch7: prospectiveQ1GiB and insideQ0 allowed; scope child/run/go exit0; GO_MARKER_PASS with actual metadata768MiB/1GiB identity and controls.'
result['run_exit']=capture.load('run-exit.json');result['go_exit']=capture.load('go-exit.json')
result['resident_guard']={k:capture.load(k+'-resident-guard.json') for k in ('run','go')}
# Additional marker, finite inventory, own cap and resource evidence audit.
index=json.loads((OUT/'LIVE-EVIDENCE-index.json').read_text())
assert len(index['inventory'])==29 and all(v['status']=='PRESENT' for v in index['inventory'].values())
inside=capture.load('inside-scope-report.json')
binding=inside['decision']['scope_binding']
marker=capture.load('marker.json')
assert marker['identity']=='ResourceMeta1G metadata marker only'
assert {k:v for k,v in marker['self_observation'].items() if k!='reads'}==binding['self_identity']
assert marker['pid']==binding['self_identity']['pid']==inside['collector_pid']
assert marker['cgroup']=='0::'+binding['self_identity']['unified_path']+'\n'
assert marker['go_report_pin']==pin(capture.raw('inside-scope-report.json'))
assert marker['source_manifest_pin']==pin((json.dumps(manifest,sort_keys=True,indent=2)+'\n').encode())
assert binding['observed_limits']==binding['expected_limits']==dict(high=768*2**20,cap=2**30,swap_max=0,tasks_max=64)
for phase in ('prospective','inside-scope'):
    d=capture.load(phase+'-report.json')['decision']
    assert d['allowed'] is True and d['projected_reserved_bytes']<55*2**30
    assert d['requested_bytes']==(2**30 if phase=='prospective' else 0)
    assert d['additional_bytes']==d['requested_bytes']
    assert d['os_control_bytes']==7*2**30 and d['margin_bytes']>2*2**30
for name in ('run','go'):
    g=capture.load(name+'-resident-guard.json')
    assert g['error'] is None and not g['cancellations']
    assert g['budget_bytes']==512*2**20 and g['peak_sampled_rss_bytes']<=g['budget_bytes']
    assert g['interval_seconds']==.02 and g['max_samples']==8192 and g['max_lineage']==256
    assert len(g['samples'])<=8192 and len(g['lineage'])<=256
result['inventory_count']=len(index['inventory'])
result['marker_audit']='PASS report/manifest hashes, PID/starttime/path identity, unified cgroup and exact controls'
result['marker']=marker
result['scope_child']=capture.load('scope-child.json')
result['collection_metrics']={p:capture.load(p+'-metrics.json') for p in ('prospective','inside-scope')}
result['evidence_scope']='New metadata capture replay only; no fresh host operation or binary identity gate; sampled peaks best effort'
u=resource.getrusage(resource.RUSAGE_SELF)
result.update(wall_seconds=time.monotonic()-start,peak_rss_bytes=u.ru_maxrss,swap=u.ru_nswap,exit=0)
assert u.ru_maxrss<512*2**20
with (OUT/'LIVE-new-data-replay.json').open('x') as f:json.dump(result,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps({k:v for k,v in result.items() if k in ('cause','exit','wall_seconds','peak_rss_bytes','swap','print_axioms')},sort_keys=True))
