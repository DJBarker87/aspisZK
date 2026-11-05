from pathlib import Path
import subprocess,sys,json,hashlib
E=Path(__file__).resolve().parent
subprocess.run([sys.executable,str(E/'NHB_make_scalar_word.py'),'low'],check=True)
borrowed=(E/'NHB_contains.rs.txt').read_text().split('#[kani::requires(n==7)]')[0]
owned=(E/'NHB_owned.rs.txt').read_text().removeprefix('use super::*;\n').split('#[kani::requires(n==11)]')[0]
caller=(E/'NHB_scalar_word.rs.txt').read_text().removeprefix('use super::*;\n')
original='self.accepted[..self.accepted_len].contains(&candidate)'
replacement='NHB_member(&self.accepted,self.accepted_len,candidate)'
assert caller.count(original)==1
caller=caller.replace(original,replacement).replace('#[kani::unwind(90)]','#[kani::unwind(24)]')
dispatch='fn NHB_member(a:&[u32;22],n:usize,x:u32)->bool {match n {\n'+''.join(f'{n}=>NHB_contains_{n}('+('*a' if n>=7 else 'a')+',n,x),\n' for n in range(11))+'_=>unreachable!(),}}\n'
attrs=''.join(f'#[kani::stub_verified(NHB_contains_{n})]\n' for n in range(11))
caller=caller.replace('fn NHB_native_word_contract()',attrs+'fn NHB_native_word_contract()')
(E/'NHB_low_composed.rs.txt').write_text(borrowed+owned+dispatch+caller)
(E/'NHB_LOW_COMPOSED.json').write_text(json.dumps(dict(domain='len<=10,draws<64; canonical, inactive zero',source_erasure=caller.replace(replacement,original).count(original)==1,closed_callees=[dict(length=n,positive=f'NHB_K{3+2*n:03}' if n<=6 else f'NHB_K{20+2*(n-7):03}',negative=f'NHB_K{4+2*n:03}' if n<=6 else f'NHB_K{21+2*(n-7):03}') for n in range(11)],status='caller must prove every requires; no unproved callee used'),indent=2)+'\n')
