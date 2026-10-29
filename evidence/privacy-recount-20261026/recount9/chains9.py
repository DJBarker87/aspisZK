from auditlib9 import *
out=[]
lines=[('ownh','20261029',list(range(63800,63854))+[63897,63898,63899]),('rdb2g','20261029',list(range(63900,63940))),('rdb2h','20261029',list(range(64300,64345))+[64397,64398,64399]),('rdcd3','20261028',list(range(60600,60700)))]
for w,d,ids in lines:
 for i in ids:
  p=f'evidence/pv-{w}-{d}/lean-{i}/receipt.json';z=json.loads(read('rw',p));ax=z.get('print_axioms',z.get('axioms',[]));ax='\n'.join(ax) if isinstance(ax,list) else ax;exit=str(z.get('exit',z.get('exit_status')))
  assert exit!='0' or 'sorryAx' not in ax,p
  names=['admission-before.json','admission-barrier.json'] if w=='rdcd3' else ['admission-launch.json','admission-barrier.json']
  gates=[]
  for name in names:
   a=f'evidence/pv-{w}-{d}/lean-{i}/{name}';v=json.loads(read('rw',a));assert v['allowed'] is True,a;gates.append(dict(evidence=a,utc=v.get('utc'),allowed=True))
  out.append(dict(line=w,attempt=i,exit=exit,credited=exit=='0',sorryAx='sorryAx' in ax,gates=gates))
fix=json.loads(read('rw','evidence/pv-fix-20261028/resume-attempts.json'))
for z in fix:
 assert z['admission_allowed'] is True and z['admission_exit']==0 and z['exit']==0
 out.append(dict(line='fixb',attempt=z['attempt'],exit=0,admission_exit=0,allowed=True))
(P/'chain-admissions9.json').write_text(json.dumps(dict(records=out,all_allowed=True,rdcd3_cooldown='independent-audit9.json#rdcd3_cooldown',scope='Entire ownh57, exact-path rdb2g40/rdb2h48, rdcd3 100 and fixb40 compiler chain. Failed elaborations uncredited; historical41466 remains void.'),indent=1)+'\n');save();print('Chain admissions',len(out),'checked')
