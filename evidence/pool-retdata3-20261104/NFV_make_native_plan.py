from pathlib import Path
import json
E=Path(__file__).resolve().parent
jobs=[]
def add(n,g,args,h,expected):jobs.append(dict(attempt=f'NFV_K{n:03}',generator=g,args=args,harness=h,expected=expected))
h='pair_forest_dispatch::NFO_read::association'
add(35,'NFV_accounts.py',['info-byte','0','positive'],h,'inconclusive-or-pass')
add(36,'NFV_accounts.py',['info-byte','0','negative'],h,'matched-control-or-inconclusive')
add(37,'NFV_accounts.py',['meta-byte','2','negative'],h,'matched-control-or-inconclusive')
n=38
for packet in ['byte',*[f'value-{i}' for i in range(8)]]:
 for control in ['positive','negative']:
  add(n,'NFV_lift_C.py',[packet,control],'pair_forest_dispatch::NFV_CJoin::association','PASS' if control=='positive' else 'intended-FAIL');n+=1
add(56,'NFV_lift_C.py',['byte','context-negative'],'pair_forest_dispatch::NFV_CJoin::association','intended-FAIL')
add(57,'NFV_lift_C.py',['byte','infos-negative'],'pair_forest_dispatch::NFV_CJoin::association','intended-FAIL')
for window,pos in [(0,58),(1,70),(2,72),(3,74),(4,76)]:
 for off,mode in [(0,'positive'),(1,'byte-negative')]:
  add(pos+off,'NFV_request_native.py',[str(window),mode],'pair_forest_dispatch::NFV_Request::association','PASS' if off==0 else 'intended-FAIL')
for n,mode in [(78,'argument-negative'),(79,'error-negative'),(80,'guard-negative')]:add(n,'NFV_request_native.py',['0',mode],'pair_forest_dispatch::NFV_Request::association','intended-FAIL')
(E/'NFV_NATIVE_PLAN.json').write_text(json.dumps(jobs,indent=1)+'\n')
