from pathlib import Path
import sys,json
E=Path(__file__).resolve().parent;sys.path.insert(0,str(E));from NEA_payload import save
p=json.loads((E/'NEA_PAYLOAD.json').read_text());s=(E/'NEA_fold.rs.txt').read_text()
s+='\nfn add_word(x:u32,y:u32)->u32{let s=x+y;if s>=P{s-P}else{s}}\nfn sub_word(x:u32,y:u32)->u32{if x>=y{x-y}else{P-y+x}}\n'
for f,g in [('add','add_word'),('sub','sub_word')]:
 s+=f'fn {f}(x:E,y:E)->E {{assert!(canon(x)&&canon(y));let a=x.to_limbs();let b=y.to_limbs();E::from_limbs(['+','.join(f'{g}(a[{i}],b[{i}])' for i in range(8))+']).unwrap()}\n'
s=s.replace('#[kani::stub(E::mul,em)]','#[kani::stub(E::add,add)]\n#[kani::stub(E::sub,sub)]\n#[kani::stub(E::mul,em)]')
p['crates/aspis-r1-cost-probe/src/NEA_fold.rs']=s
p['crates/aspis-r1-cost-probe/src/NEA_fold_reference.rs']=(E/'NEA_fold_reference.rs.txt').read_text().replace('#![no_std]\n','')
save(p);(E/'NEA_fold_linear.rs.txt').write_text(s)
