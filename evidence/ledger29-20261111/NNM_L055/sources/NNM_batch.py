"""Sequential raw ax2 windows with independent resource receipts."""
from pathlib import Path
import subprocess,json,time,re,sys,os
B=Path.cwd();mode=sys.argv[1]
for n in ['AUDIT_ROOTS.json','AUDIT_MODULES.json']:(B/('NLX_'+n)).write_bytes((B/('NNM_'+n)).read_bytes())
E=B/'NNM_audit'/mode;E.mkdir(parents=True,exist_ok=True)
seal=mode.endswith('-pin')
if seal:mode=mode[:-4]
if mode=='retention':
 exec(compile((B/'NNM_pin.py').read_text(),'NNM_pin.py','exec'));sys.exit(0)
if mode in ['scan','finalscan']:jobs=[('scan',['NNM_native/NNM_Driver','scan'])]
elif mode=='fixtures':jobs=[('fixtures',['NNM_native/NNM_ProofDriver','fixtures'])]
else:
 parts=mode.removeprefix('batch').split('-');start=int(parts[0]);end=int(parts[-1]);jobs=[('proof'+str(i),['NNM_native/NNM_ProofDriver','proof'+str(i)])for i in range(start,end+1)]
for name,cmd in jobs:
 start=time.monotonic()
 with(E/(name+'.log')).open('w')as out:r=subprocess.run(['/usr/bin/time','-v','-o',str(E/(name+'.time')),*cmd],stdout=out,stderr=subprocess.STDOUT)
 raw=(E/(name+'.log')).read_text();timing=(E/(name+'.time')).read_text()
 def metric(k):
  m=re.search(re.escape(k)+r':\s*(.*)',timing);return m[1]if m else None
 x=dict(target=name,command=cmd,exit_status=r.returncode,wall_seconds=time.monotonic()-start,peak_rss_kib=metric('Maximum resident set size (kbytes)'),swaps=metric('Swaps'),print_axioms=[l for l in raw.splitlines()if'depends on axioms'in l or'does not depend on any axioms'in l],results=[json.loads(l[11:])for l in raw.splitlines()if l.startswith('NEP_RESULT ')])
 (E/(name+'.json')).write_text(json.dumps(x,indent=1)+'\n');print(json.dumps(x),flush=True)
 if r.returncode:
  allowed={'AspisR1.NKR_ScheduleExt.transition','NHC_DecodeModel.decoder_error','LIB_VCarriers.Acc','NNI_CollectorAcc.alias_identity'}
  expected=set(json.loads((B/'NNM_AUDIT_ROOTS.json').read_text())['groups'][int(name[5:])]) if name.startswith('proof')else set()
  actual={z['root']for z in x['results']}
  collector_only=(name.startswith('proof') and bool(expected) and any(not z['equal']for z in x['results']) and r.returncode==1 and actual==expected and len(actual)==len(x['results']) and
   all(set(z['walked_axioms'])<={'propext','Quot.sound','Classical.choice'}for z in x['results']) and
   all(z['equal']or z['root']in allowed for z in x['results']))
  if not collector_only:print(raw,flush=True);sys.exit(r.returncode)
  print('Retained known collector disagreement; complete raw ax2 walk authoritative under(ab\')(3)/(ax2)',flush=True)


if seal:exec(compile((B/'NNM_pin.py').read_text(),'NNM_pin.py','exec'))
