from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;x=json.loads((E/'NGH_NATIVE_INPUTS.json').read_text())
n='crates/aspis-core/src/field.rs';s=x[n]
line=next(l for l in s.splitlines()if l.startswith('#[cfg_attr(kani,kani::ensures(|r| (((r[NGH_reference::OBS'))
s=s.replace(line,'#[cfg_attr(kani,kani::ensures(|r| NGH_reference::bound_result(*r,sums)!=cfg!(NGH_invert)))]')
x[n]=s
n='crates/aspis-core/src/NGH_reference.rs';s=x[n]
a=s.index('fn one(cell:usize');b=s.index('\npub(super) fn progress',a)
s=s[:a]+'''fn one(_cell:usize,now:u64,old:u64,_a:M31,_b:M31,done:bool)->bool{
 if done{now<=old+4611686009837453316}else{now==old}
}
'''+s[b:]
s+='\npub(super) fn bound_result(s:[[u64;3];3],old:[[u64;3];3])->bool{\n'+ '&&\n'.join(f' s[{i}][{j}]<=old[{i}][{j}]+4611686009837453316'for i in range(3)for j in range(3))+'\n}\n'
x[n]=s
(E/'NGH_BOUND_INPUTS.json').write_text(json.dumps(x,indent=1)+'\n');(E/'NGH_BOUND_PINS.json').write_text(json.dumps({n:hashlib.sha256(t.encode()).hexdigest()for n,t in x.items()},indent=1)+'\n');(E/'NGH_reference_bounds.rs.txt').write_text(s)
