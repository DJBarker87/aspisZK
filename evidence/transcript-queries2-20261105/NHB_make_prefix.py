from pathlib import Path
E=Path(__file__).resolve().parent
out=['use super::*;\n']
for n in range(11,23):
 pred=' || '.join('a[%d]==x'%i for i in range(n))
 out.append(f'''#[kani::requires(n=={n})]
#[kani::ensures(|out| *out == ({pred}))]
fn NHB_contains_{n}(a:&[u32;{n}],n:usize,x:u32)->bool {{
 let result=a[..{n}].contains(&x);
 #[cfg(not(NHB_invert))] {{result}}
 #[cfg(NHB_invert)] {{!result}}
}}
#[kani::proof_for_contract(NHB_contains_{n})]
#[kani::unwind(90)]
#[kani::stub(core::ptr::copy_nonoverlapping,crate::KMX_stubs::KMX_copy_nonoverlapping)]
fn NHB_contains_{n}_contract() {{
 let a:[u32;{n}]=kani::any();let n:usize=kani::any();let x:u32=kani::any();
 NHB_contains_{n}(&a,n,x);
}}
''')
(E/'NHB_prefix.rs.txt').write_text(''.join(out))
