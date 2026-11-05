from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent
for src,label in [('INVERSE','ARG_CM'),('QINVERSE','ARG_Q')]:
 x=json.loads((E/f'NHH_{src}_INPUTS.json').read_text());n='crates/aspis-r1-cost-probe/src/NHH_fields.rs';s=x[n]
 old='let out=NHH_fixed(&mut log,input);';new=old+'\n if cfg!(NHH_bad_argument){log.events[0].a=if input.a.0==0{M31(1)}else{M31(0)};}';assert s.count(old)==1;s=s.replace(old,new)
 if src=='QINVERSE':
  old='let out=NHH_try(&mut log,input);';new=old+'\n if cfg!(NHH_bad_argument)&&!input.is_zero(){log.events[0].a.a=if input.c0.a.0==0{M31(1)}else{M31(0)};}';assert s.count(old)==1;s=s.replace(old,new)
  old='let out=NHH_inv_wrapper(&mut log,input);';new=old+'\n if cfg!(NHH_bad_argument){if let Some((seen,_))=log.as_mut(){seen.c0.a=if input.c0.a.0==0{M31(1)}else{M31(0)};}}';assert s.count(old)==1;s=s.replace(old,new)
 x[n]=s;(E/f'NHH_{label}_INPUTS.json').write_text(json.dumps(x));(E/f'NHH_{label}_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()},indent=1)+'\n')
 (E/f'NHH_{label}.rs.txt').write_text(s)
