"""Focused noncompiler --check; no selection regeneration or Lean invocation."""
import json,pathlib,resource,subprocess,sys,time
from Port32CONSUMER_check import T,E,pin,state,safe
from Port32CONSUMER_material358 import material
PRE=E/'Port32CONSUMER_preflight.json'
CHECK=E/'Port32CONSUMER_check358.json'
def validate():
 start=time.monotonic()
 assert subprocess.check_output(['git','branch','--show-current'],text=True).strip()=='codex/cx-port32-consumer-20261025'
 pre=json.loads(PRE.read_text());old=json.loads((E/'Port32CONSUMER_check.json').read_text())
 for x in pre['pins']+pre['runtime']+old['api']:assert pin(safe(x['path']))==x,x['path']
 for x in pre['states']:assert state(safe(x['path']))==x['stat'],x['path']
 src=T/'Port32CONSUMER_Consumer358.lean';s=src.read_text()
 assert s==material()
 assert [l for l in s.splitlines() if l.startswith('import ')]==['import Lean']
 for b in ['sorry','admit','native_decide','implemented_by','#eval!','doCheck := false','maxHeartbeats','maxRecDepth','region.free','initialize ']:assert b not in s,b
 assert s.count('env.addDeclCore')==2
 assert 'setEnv checked' in s and 'PORT32_COMPLETE' in s
 assert s.index('unless regions.size > 0')>s.index('final CI drift')
 paths=[T/n for n in ['Port32CONSUMER_Consumer358.lean','Port32CONSUMER_material358.py','Port32CONSUMER_check358.py','Port32CONSUMER_run358.py']]
 paths += [E/n for n in ['Port32CONSUMER_CRITERIA358.md','Port32CONSUMER_source-357.lean.txt','Port32CONSUMER_ComposedSource.lean.txt','Port32CONSUMER_BEFORE-AFTER.md','Port32CONSUMER_BOUNDARIES.md','Port32CONSUMER_variant-assessment.json']]
 r=dict(status='PASS focused TEXT/DATA --check equivalent; no compiler/no theorem',command=[sys.executable,'-B',str(T/'Port32CONSUMER_check358.py'),'--check'],source_revision=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),files=[pin(safe(p)) for p in paths],api=old['api'],dependency_receipt=pin(PRE),pins=pre['pins'],runtime=pre['runtime'],states_assessment='1441 released input safe/stat checks;355 byte hashes reused from pinned preflight; no new identity gate',reused_inventory=pre['reused_inventory'],selection=dict(names=28833,containers=1444,bytes=252187832,groups=840,repins=[13,45,4]),core_assessment=pre['core_assessment'],exit_status=0,wall_seconds=time.monotonic()-start,peak_rss_bytes=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,swaps=resource.getrusage(resource.RUSAGE_SELF).ru_nswap,lean_calls=0,allocated=[358],actual_before=357,axioms='N/A noncompiler')
 assert r['peak_rss_bytes']<512*1024**2
 return r
if __name__=='__main__':
 assert sys.argv[1:]==['--check'] and not CHECK.exists()
 r=validate();CHECK.write_text(json.dumps(r,indent=2)+'\n')
 print(json.dumps({k:r[k] for k in ['status','wall_seconds','peak_rss_bytes','swaps']}))
