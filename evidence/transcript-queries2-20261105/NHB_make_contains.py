from pathlib import Path
E=Path(__file__).resolve().parent
out=['use super::*;\n']
for n in range(23):
 pred=' || '.join('a[%d]==x'%i for i in range(n)) or 'false'
 out.append(f'''#[kani::requires(n=={n})]
#[kani::ensures(|out| *out == ({pred}))]
fn NHB_contains_{n}(a:&[u32;22],n:usize,x:u32)->bool {{
 let result=a[..n].contains(&x);
 #[cfg(not(NHB_invert))] {{result}}
 #[cfg(NHB_invert)] {{!result}}
}}
#[kani::proof_for_contract(NHB_contains_{n})]
#[kani::unwind(24)]
fn NHB_contains_{n}_contract() {{
 let a:[u32;22]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_{n}(&a,n,x);
}}
''')
(E/'NHB_contains.rs.txt').write_text(''.join(out))
