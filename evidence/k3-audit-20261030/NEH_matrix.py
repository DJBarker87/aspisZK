from pathlib import Path
import subprocess,os,json
E=Path(__file__).resolve().parent
cases=[
 ('004',dict(NEH_TYPE='Observer',NEH_LITERAL='None',NEH_PRED='obs.is_some()')),
 ('005',dict(NEH_TYPE='Option<core::num::NonZeroUsize>',NEH_LITERAL='None',NEH_PRED='obs.is_some()')),
 ('006',dict(NEH_TYPE='Option<&u8>',NEH_LITERAL='None',NEH_PRED='obs.is_some()')),
 ('007',dict(NEH_TYPE='[usize;1]',NEH_LITERAL='[0]',NEH_PRED='obs[0]==1')),
 ('008',dict(NEH_INIT='1',NEH_WRITE='2',NEH_LITERAL='1',NEH_PRED='obs==2')),
 ('009',dict(NEH_INIT='0',NEH_WRITE='2',NEH_LITERAL='1',NEH_PRED='obs==2')),
 ('010',dict(NEH_MODE='cell')),
 ('011',dict(NEH_MODE='unwritten')),
 ('012',dict(NEH_MODE='local')),
 ('013',dict(NEH_TYPE='[u8;8]',NEH_LITERAL='[0;8]',NEH_PRED='obs[0]==1')),
 ('014',dict(NEH_TYPE='u8',NEH_LITERAL='0',NEH_PRED='obs==1')),
 ('015',dict(NEH_INIT='0x0101010101010101',NEH_WRITE='0x0202020202020202',NEH_TYPE='[u8;8]',NEH_LITERAL='[1;8]',NEH_PRED='obs[0]==2')),
 ('016',dict(NEH_MODE='cell',NEH_TYPE='Option<core::num::NonZeroUsize>',NEH_LITERAL='None',NEH_PRED='obs.is_some()')),
 ('017',dict(NEH_MODE='unwritten',NEH_TYPE='Option<core::num::NonZeroUsize>',NEH_LITERAL='None',NEH_PRED='obs.is_some()')),
]
for n,env in cases:
 a='NEH_K'+n
 with (E/(a+'-driver.log')).open('w') as f:
  r=subprocess.run(['python3',str(E/'NEH_experiments.py'),a],env={**os.environ,**env},stdout=f,stderr=subprocess.STDOUT)
 print(a,r.returncode,flush=True)
 if r.returncode:raise SystemExit('driver failure; inspect, do not skip')
