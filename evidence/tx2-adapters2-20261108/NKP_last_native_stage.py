from NKP_lane_prefix import attempt as lane
from NKP_registry import attempt as registry
import lzma,json
from NKP_transport import E
n=72
results=json.loads((E/'NKP_LAST_NATIVE_RESULTS.json').read_text())
for part,fun in [('registry1',registry),('registry2',registry),('entry1',registry),('entry2',registry)]:
 for mode in ['positive','inverse']:
  a=f'NKP_K{n:03}';rc=fun(a,part,mode);n+=1
  log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
  results.append(dict(attempt=a,part=part,mode=mode,exit=rc['exit_status'],timeout='timed out' in log,semantic_failure='Failed Checks:' in log and 'timed out' not in log))
  (E/'NKP_LAST_NATIVE_RESULTS.json').write_text(json.dumps(results,indent=1)+'\n')
print('LAST_NATIVE_STAGE_COMPLETE',flush=True)
