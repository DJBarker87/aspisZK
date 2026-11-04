from pathlib import Path
import json,hashlib
E=Path(__file__).resolve().parent;x=json.loads((E/'NGH_NATIVE_INPUTS.json').read_text())
n='crates/aspis-core/src/field.rs';s=x[n]
s=s.replace('#[cfg_attr(kani,kani::ensures(|r| (*r==NGH_reference::NGH_accumulate_ref(sums,left,right))!=cfg!(NGH_invert)))]', '''#[cfg_attr(kani,kani::modifies())]
#[cfg_attr(kani,kani::ensures(|r| (r[NGH_reference::OBS/3][NGH_reference::OBS%3]==NGH_reference::NGH_accumulate_ref(sums,left,right)[NGH_reference::OBS/3][NGH_reference::OBS%3])!=cfg!(NGH_invert)))]''')
x[n]=s
n='crates/aspis-core/src/NGH_reference.rs';s=x[n]
s+='\npub(super) const OBS:usize='+''.join(f'if cfg!(NGH_observe_{i}){{{i}}}else{{' for i in range(1,9))+'0'+'}'*8+';\n'
s=s.replace('fn one(now:u64,old:u64,a:M31,b:M31,done:bool)->bool{now==old+if done{native_product(a.0 as u64,b.0 as u64)}else{0}}', '''fn one(cell:usize,now:u64,old:u64,a:M31,b:M31,done:bool)->bool{
 if cell==OBS{now==old+if done{native_product(a.0 as u64,b.0 as u64)}else{0}}
 else if done{now<=old+4611686009837453316}else{now==old}
}''')
for i in range(3):
 for j in range(3):s=s.replace(f'one(s[{i}][{j}],',f'one({3*i+j},s[{i}][{j}],')
x[n]=s
(E/'NGH_NATIVE_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');(E/'NGH_SOURCE_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()},indent=1)+'\n');(E/'NGH_reference_window.rs.txt').write_text(s)
p=E/'NGH_run.py';s=p.read_text().replace("if os.environ.get('NGH_FOR'):env['RUSTFLAGS']+=' --cfg NGH_for_diagnostic'", "if os.environ.get('NGH_FOR'):env['RUSTFLAGS']+=' --cfg NGH_for_diagnostic'\n if os.environ.get('NGH_OBSERVE'):env['RUSTFLAGS']+=' --cfg NGH_observe_'+os.environ['NGH_OBSERVE']")
p.write_text(s)
