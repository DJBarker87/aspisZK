from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
base=(E/'NEF_false_pass.rs.txt').read_text()
cases=[('004','nonzero',base.replace('obs:Observer','obs:Option<core::num::NonZeroUsize>')),
 ('005','reference',base.replace('obs:Observer','obs:Option<&u8>')),
 ('006','array',base.replace('obs:Observer','obs:[usize;1]').replace('obs.is_some()','obs[0]==1').replace('NBZ_mark_none(None,','NBZ_mark_none([0usize;1],')),
 ('007','scalar',base.replace('obs:Observer','obs:usize').replace('obs.is_some()','obs==1').replace('NBZ_mark_none(None,','NBZ_mark_none(0,'))]
for num,label,s in cases:
 p=E/('NEF_root_'+label+'.rs.txt');p.write_text(s)
 for args in [['NEF_update.py','NEF_UP'+num,'crates/aspis-r1-cost-probe/src/NBZ_native.rs',p.name],['NEF_run.py','NEF_K'+num,'kani','verifier::candidate::NBZ_native::NBZ_return_carriers']]:
  r=subprocess.run([sys.executable,str(E/args[0]),*args[1:]])
  assert r.returncode==0,(label,args,r.returncode)
