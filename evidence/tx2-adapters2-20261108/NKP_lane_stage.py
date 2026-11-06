from NKP_lane import *
import lzma
n=47
plans=[('constructor',0,'inverse')]+[(p,f,m) for p,fs in [('constructor',range(1,6)),('iteration',range(4))] for f in fs for m in ['positive','inverse']]
results=[]
for part,field,mode in plans:
 a=f'NKP_K{n:03}';rc=attempt(a,part,field,mode);n+=1
 log=lzma.decompress((E/a/'stdout.log.xz').read_bytes()).decode()
 results.append(dict(attempt=a,part=part,field=field,mode=mode,exit=rc['exit_status'],timeout='timed out' in log,expected=(rc['exit_status']==0 if mode=='positive' else rc['exit_status']!=0 and 'Failed Checks:' in log and 'timed out' not in log)))
 (E/'NKP_LANE_RESULTS.json').write_text(json.dumps(results,indent=1)+'\n')
 # Every source shape is submitted once; continue independent windows on failure.
print('LANE_STAGE_COMPLETE',flush=True)
