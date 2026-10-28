from NCN_extend import extend,attrs,E
import json,subprocess,hashlib
s=subprocess.check_output(['git','show','4bb3b3f5:crates/aspis-r1-cost-probe/src/verifier.rs'],text=True)
start=s.index('        let old=residue_limb_at(row,j);');end=s.index('\n    }',start)
body=s[start:end]
assert body=='''        let old=residue_limb_at(row,j);
        let limb=power_limb_at(&limbs,j);
        row[j]=old+u64::from(limb)*u64::from(basis.0);'''
h='\n#[cfg(kani)] mod NCN_update {\nuse super::*;\n'
h+='fn iteration(row:&mut[u64;4],limbs:&[u32;4],basis:M31,j:usize){\n'+body+'\n}\n'
for neg in [False,True]:
 name='step_'+('wrong' if neg else 'ok')
 h+=attrs+f'''fn {name}(){{
let mut row:[u64;4]=kani::any();let limbs:[u32;4]=kani::any();let basis=M31(kani::any());let j:usize=kani::any();let k:usize=kani::any();let terms:usize=kani::any();
kani::assume(j<4&&k<4&&k!=j);kani::assume(limbs[j]<2147483647&&basis.0<2147483647);
kani::assume(row[j]<17179869184+(terms%4)*4611686009837453316);
let old=row[j];let frame=row[k];let product=u64::from(limbs[j])*u64::from(basis.0);
iteration(&mut row,&limbs,basis,j);
assert!(row[j]{'!=' if neg else '=='}old+product);assert!(row[k]==frame);
}}\n'''
h+='}\n';extend('NCN_update.patch',h)
(E/'NCN_UPDATE_SOURCE.json').write_text(json.dumps(dict(frozen='4bb3b3f51e16b4525f1d10336e2b0bcbbd775387',body=body,sha256=hashlib.sha256(body.encode()).hexdigest(),scope='one arbitrary native product/add/write; no field multiplication'),indent=2)+'\n')
