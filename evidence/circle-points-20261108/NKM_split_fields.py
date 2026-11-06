from pathlib import Path
import base64,json,hashlib
E=Path(__file__).resolve().parent;p=E/'NKM_CONTRACT_OVERLAY.json';d=json.loads(p.read_text());n='crates/aspis-r1-cost-probe/src/NKM_native.rs';r=d[n];s=base64.b64decode(r['data']).decode();before=r['sha256']
s=s.replace('a as u64+b as u64','(a as u64).wrapping_add(b as u64)').replace('a as u64+P as u64-b as u64','(a as u64).wrapping_add(P as u64).wrapping_sub(b as u64)').replace('a as u64*b as u64','(a as u64).wrapping_mul(b as u64)')
s+='''
// One callee boundary on an arbitrary canonical pre-state; all five field kinds.
#[kani::proof] #[kani::unwind(40)]
#[kani::stub(core::ptr::copy_nonoverlapping,KMX_copy_nonoverlapping)]
fn field_boundary(){
 let a=q(kani::any());let b=q(kani::any());kani::assume(canonical(a)&&canonical(b));
 let kind:u8=kani::any();kani::assume(kind<=4);
 let mut l=new_log(kani::any());let out=event(&mut l,kind,a,b);
 assert_eq!(l.len,1);assert_eq!(l.events[0],Event{kind,a,b,out});
 check(out==l.replies[0]);
}
'''
r.update(before=before,sha256=hashlib.sha256(s.encode()).hexdigest(),data=base64.b64encode(s.encode()).decode());p.write_text(json.dumps(d))
p=E/'NKM_SOURCE_PINS.json';pins=json.loads(p.read_text());pins[n]=r['sha256'];p.write_text(json.dumps(pins,indent=2)+'\n')
(E/'NKM_SPLIT_OVERLAY.json').write_text(json.dumps(dict(path=n,**r)))
for i,negative in [(26,False),(27,True)]:
 x=json.loads((E/'NKM_K025.json').read_text());a=f'NKM_K{i:03}';x['attempt']=a;x['command'][2]=a+'.json';x['module']='NKM_native::field_boundary';x['native_command'][x['native_command'].index('--harness')+1]=x['module'];x['env']['RUSTFLAGS']='-Copt-level=3 -C link-arg=-Wl,--threads=1'+(' --cfg NKM_invert'if negative else '');x['negative_control']=negative;x['collect']=[n.replace('NKM_K025',a)for n in x['collect']];x['expected_time']='Split one field callee boundary from K025; natural-spec computation has wrapping machine arithmetic on the proved canonical domain, avoiding arithmetic safety assertions inside assumed specs';(E/(a+'.json')).write_text(json.dumps(x))
