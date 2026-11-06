from pathlib import Path
import json
E=Path(__file__).resolve().parent;p=E/'NJB_active.rs.txt';s=p.read_text();old='let c:usize=kani::any();kani::assume(c<7);let mut log';new='let c:usize='+''.join(('if'if i==0 else'else if')+f' cfg!(NJB_coordinate_{i})'+'{'+str(i)+'}'for i in range(7))+'else{panic!("select one coordinate partition")};let mut log';assert s.count(old)==1;s=s.replace(old,new);p.write_text(s)
x=json.loads((E/'NJB_L018.json').read_text());x['attempt']='NJB_L029';x['expected_time']='Split timed-out seven-way low-step harness into seven constant-coordinate domains, same name/body/property; no timeout increase';(E/'NJB_L029.json').write_text(json.dumps(x))
for c in range(7):
 for neg in range(2):
  i=20+2*c+neg;a=f'NJB_K{i:03}';x=json.loads((E/'NJB_K010.json').read_text());old=x['attempt'];x['attempt']=a;x['command'][-1]=a+'.json';x['collect']=[v.replace(old,a)for v in x['collect']];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1 --cfg NJB_coordinate_'+str(c)+(' --cfg NJB_invert'if neg else'');x['expected_time']='Optimized active-low single coordinate '+str(c)+' after seven-way timeout; identical native target name and assertion';x['partition']={'coordinate':c,'covered_union':'all Fin 7'};(E/(a+'.json')).write_text(json.dumps(x))
print('seven low-coordinate partitions configured; same harness name and assertions, original timeout excluded')
