#![feature(allocator_api)]
extern crate alloc;
include!("KMX_stubs.rs");
fn differential<T:Copy+Eq+core::fmt::Debug>(src:&[T],seed:T)->usize{
 let mut checks=0;
 for offset in [0,1,3] {
  let mut real=vec![seed;src.len()+offset+2];let mut stub=real.clone();
  real[offset..offset+src.len()].copy_from_slice(src);KMX_copy_from_slice(&mut stub[offset..offset+src.len()],src);assert_eq!(real,stub);checks+=1;
  real.fill(seed);stub.fill(seed);real[offset..offset+src.len()].clone_from_slice(src);KMX_clone_from_slice(&mut stub[offset..offset+src.len()],src);assert_eq!(real,stub);checks+=1;
  real.fill(seed);stub.fill(seed);unsafe{core::ptr::copy_nonoverlapping(src.as_ptr(),real.as_mut_ptr().add(offset),src.len());KMX_copy_nonoverlapping(src.as_ptr(),stub.as_mut_ptr().add(offset),src.len())};assert_eq!(real,stub);checks+=1;
 }
 for capacity in [0,1,src.len(),src.len()+3] {
  let mut real=Vec::with_capacity(capacity);real.push(seed);let mut stub=Vec::with_capacity(capacity);stub.push(seed);
  real.extend_from_slice(src);KMX_extend_from_slice(&mut stub,src);assert_eq!(real,stub);checks+=1;
 }
 assert_eq!(src.to_vec(),KMX_to_vec(src));checks+1
}
fn realloc_compare(src:&[u8])->usize{
 if src.is_empty(){return 0;}let mut checks=0;
 for new_size in [1,src.len(),src.len()+1,src.len()*2+3]{unsafe{
  let layout=alloc::alloc::Layout::array::<u8>(src.len()).unwrap();
  let a=alloc::alloc::alloc(layout);let b=alloc::alloc::alloc(layout);assert!(!a.is_null()&&!b.is_null());
  for i in 0..src.len(){a.add(i).write(src[i]);b.add(i).write(src[i]);}
  let a=alloc::alloc::realloc(a,layout,new_size);let b=KMX_realloc(b,layout,new_size);assert!(!a.is_null()&&!b.is_null());
  for i in 0..src.len().min(new_size){assert_eq!(a.add(i).read(),b.add(i).read());}
  let layout=alloc::alloc::Layout::array::<u8>(new_size).unwrap();alloc::alloc::dealloc(a,layout);alloc::alloc::dealloc(b,layout);checks+=1;
 }}checks
}
fn random(state:&mut u64)->u64{*state^=*state<<13;*state^=*state>>7;*state^=*state<<17;*state}
#[derive(Clone,Copy,Eq,PartialEq,Debug)]struct Pair{a:u32,b:u32}
#[derive(Clone,Copy,Eq,PartialEq,Debug)]struct KMX_Pair{a:u32,b:u32}
fn main(){
{let mut input=[0u8;1];input[0]=1u8;let n:usize=1;let mut level=[0u8;1];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[0],1u8,"KMX_c000_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c000");}
{let mut input=[0u8;2];input[1]=1u8;let n:usize=2;let mut level=[0u8;2];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[1],1u8,"KMX_c001_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c001");}
{let mut input=[0u8;3];input[2]=1u8;let n:usize=3;let mut level=[0u8;3];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[2],1u8,"KMX_c002_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c002");}
{let mut input=[0u8;4];input[3]=1u8;let n:usize=4;let mut level=[0u8;4];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[3],1u8,"KMX_c003_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c003");}
{let mut input=[0u8;8];input[7]=1u8;let n:usize=8;let mut level=[0u8;8];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[7],1u8,"KMX_c004_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c004");}
{let mut input=[0u8;16];input[15]=1u8;let n:usize=16;let mut level=[0u8;16];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[15],1u8,"KMX_c005_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c005");}
{let mut input=[0u32;1];input[0]=512u32;let n:usize=1;let mut level=[0u32;1];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[0],512u32,"KMX_c006_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c006");}
{let mut input=[0u32;2];input[1]=512u32;let n:usize=2;let mut level=[0u32;2];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[1],512u32,"KMX_c007_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c007");}
{let mut input=[0u32;3];input[2]=512u32;let n:usize=3;let mut level=[0u32;3];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[2],512u32,"KMX_c008_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c008");}
{let mut input=[0u32;4];input[3]=512u32;let n:usize=4;let mut level=[0u32;4];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[3],512u32,"KMX_c009_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c009");}
{let mut input=[0u32;8];input[7]=512u32;let n:usize=8;let mut level=[0u32;8];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[7],512u32,"KMX_c010_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c010");}
{let mut input=[0u32;16];input[15]=512u32;let n:usize=16;let mut level=[0u32;16];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[15],512u32,"KMX_c011_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c011");}
{let mut input=[0u64;1];input[0]=512u64;let n:usize=1;let mut level=[0u64;1];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[0],512u64,"KMX_c012_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c012");}
{let mut input=[0u64;2];input[1]=512u64;let n:usize=2;let mut level=[0u64;2];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[1],512u64,"KMX_c013_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c013");}
{let mut input=[0u64;3];input[2]=512u64;let n:usize=3;let mut level=[0u64;3];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[2],512u64,"KMX_c014_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c014");}
{let mut input=[0u64;4];input[3]=512u64;let n:usize=4;let mut level=[0u64;4];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[3],512u64,"KMX_c015_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c015");}
{let mut input=[0u64;8];input[7]=512u64;let n:usize=8;let mut level=[0u64;8];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[7],512u64,"KMX_c016_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c016");}
{let mut input=[0u64;16];input[15]=512u64;let n:usize=16;let mut level=[0u64;16];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[15],512u64,"KMX_c017_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c017");}
{let mut input=[[0u8;32];1];input[0]=[1u8;32];let n:usize=1;let mut level=[[0u8;32];1];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[0],[1u8;32],"KMX_c018_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c018");}
{let mut input=[[0u8;32];2];input[1]=[1u8;32];let n:usize=2;let mut level=[[0u8;32];2];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[1],[1u8;32],"KMX_c019_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c019");}
{let mut input=[[0u8;32];3];input[2]=[1u8;32];let n:usize=3;let mut level=[[0u8;32];3];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[2],[1u8;32],"KMX_c020_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c020");}
{let mut input=[[0u8;32];4];input[3]=[1u8;32];let n:usize=4;let mut level=[[0u8;32];4];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[3],[1u8;32],"KMX_c021_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c021");}
{let mut input=[[0u8;32];8];input[7]=[1u8;32];let n:usize=8;let mut level=[[0u8;32];8];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[7],[1u8;32],"KMX_c022_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c022");}
{let mut input=[[0u8;32];16];input[15]=[1u8;32];let n:usize=16;let mut level=[[0u8;32];16];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[15],[1u8;32],"KMX_c023_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c023");}
{let mut input=[KMX_Pair{a:0,b:0};1];input[0]=KMX_Pair{a:512,b:1};let n:usize=1;let mut level=[KMX_Pair{a:0,b:0};1];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[0],KMX_Pair{a:512,b:1},"KMX_c024_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c024");}
{let mut input=[KMX_Pair{a:0,b:0};2];input[1]=KMX_Pair{a:512,b:1};let n:usize=2;let mut level=[KMX_Pair{a:0,b:0};2];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[1],KMX_Pair{a:512,b:1},"KMX_c025_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c025");}
{let mut input=[KMX_Pair{a:0,b:0};3];input[2]=KMX_Pair{a:512,b:1};let n:usize=3;let mut level=[KMX_Pair{a:0,b:0};3];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[2],KMX_Pair{a:512,b:1},"KMX_c026_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c026");}
{let mut input=[KMX_Pair{a:0,b:0};4];input[3]=KMX_Pair{a:512,b:1};let n:usize=4;let mut level=[KMX_Pair{a:0,b:0};4];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[3],KMX_Pair{a:512,b:1},"KMX_c027_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c027");}
{let mut input=[KMX_Pair{a:0,b:0};8];input[7]=KMX_Pair{a:512,b:1};let n:usize=8;let mut level=[KMX_Pair{a:0,b:0};8];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[7],KMX_Pair{a:512,b:1},"KMX_c028_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c028");}
{let mut input=[KMX_Pair{a:0,b:0};16];input[15]=KMX_Pair{a:512,b:1};let n:usize=16;let mut level=[KMX_Pair{a:0,b:0};16];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[15],KMX_Pair{a:512,b:1},"KMX_c029_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c029");}
{let mut input=[0u8;64];input[63]=1u8;let n:usize=64;let mut level=[0u8;64];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[63],1u8,"KMX_c030_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c030");}
{let mut input=[0u32;16];input[15]=512u32;let n:usize=16;let mut level=[0u32;16];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[15],512u32,"KMX_c031_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c031");}
{let mut input=[0u8;128];input[127]=1u8;let n:usize=128;let mut level=[0u8;128];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[127],1u8,"KMX_c032_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c032");}
{let mut input=[0u32;32];input[31]=512u32;let n:usize=32;let mut level=[0u32;32];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[31],512u32,"KMX_c033_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c033");}
{let mut input=[0u8;1024];input[1023]=1u8;let n:usize=1024;let mut level=[0u8;1024];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[1023],1u8,"KMX_c034_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c034");}
{let mut input=[0u32;256];input[255]=512u32;let n:usize=256;let mut level=[0u32;256];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[255],512u32,"KMX_c035_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c035");}
{let mut input=[0u8;1736];input[1735]=1u8;let n:usize=1736;let mut level=[0u8;1736];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[1735],1u8,"KMX_c036_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c036");}
{let mut input=[0u32;434];input[433]=512u32;let n:usize=434;let mut level=[0u32;434];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[433],512u32,"KMX_c037_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c037");}
{let mut input=[0u8;1768];input[1767]=1u8;let n:usize=1768;let mut level=[0u8;1768];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[1767],1u8,"KMX_c038_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c038");}
{let mut input=[0u32;442];input[441]=512u32;let n:usize=442;let mut level=[0u32;442];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[441],512u32,"KMX_c039_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c039");}
{let mut input=[0u32;16];input[15]=512u32;let n:usize=16;let mut level=[0u32;16];unsafe{core::ptr::copy_nonoverlapping(input.as_ptr(),level.as_mut_ptr().add(0),n);}assert_eq!(level[15],512u32,"KMX_c040_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c040");}
{let mut input=[0u32;16];input[15]=512u32;let n:usize=16;let mut level=[0u32;16];level[0..0+n].clone_from_slice(&input[..n]);assert_eq!(level[15],512u32,"KMX_c041_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c041");}
{let mut input=[0u32;16];input[15]=512u32;let n:usize=16;let mut level=Vec::<u32>::with_capacity(16);level.extend_from_slice(&input[..n]);assert_eq!(level[15],512u32,"KMX_c042_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c042");}
{let mut input=[0u32;16];input[15]=512u32;let n:usize=16;let level=input[..n].to_vec();assert_eq!(level[15],512u32,"KMX_c043_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c043");}
{let mut input=[0u32;16];input[15]=512u32;let n:usize=16;let mut level=Vec::<u32>::with_capacity(1);level.push(0u32);level.extend_from_slice(&input[..n]);assert_eq!(level[16],512u32,"KMX_c044_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c044");}
{let mut input=[0u32;16];input[15]=512u32;let n:usize=16;let mut level=[0u32;17];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[15],512u32,"KMX_c045_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c045");}
{let mut input=[0u32;16];input[15]=512u32;let n:usize=16;let mut level=[0u32;18];level[1..1+n].copy_from_slice(&input[..n]);assert_eq!(level[16],512u32,"KMX_c046_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c046");}
{let mut input=[0u32;16];input[15]=512u32;let n:usize=16;let mut level=[0u32;24];level[3..3+n].copy_from_slice(&input[..n]);assert_eq!(level[18],512u32,"KMX_c047_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c047");}
{let mut input=[0u32;16];input[15]=512u32;let n:usize=16;let mut level=vec![0u32;16];level[0..0+n].copy_from_slice(&input[..n]);assert_eq!(level[15],512u32,"KMX_c048_correct");println!("KMX_NATIVE_CONFIG_PASS KMX_c048");}
 let mut checks=0usize;let vals=[0u32,1,255,256,512];
 for n in 0..=6 {for mut code in 0..5usize.pow(n as u32) {let mut src=vec![0u32;n];for x in &mut src{*x=vals[code%5];code/=5;}checks+=differential(&src,0);
 let b:Vec<u8>=src.iter().map(|x|(*x/256+*x%256) as u8).collect();checks+=differential(&b,0);checks+=realloc_compare(&b);
 let b:Vec<u64>=src.iter().map(|x|*x as u64).collect();checks+=differential(&b,0);
 let b:Vec<[u8;32]>=src.iter().map(|x|[(*x/256+*x%256) as u8;32]).collect();checks+=differential(&b,[0;32]);
 let b:Vec<Pair>=src.iter().map(|x|Pair{a:*x,b:*x}).collect();checks+=differential(&b,Pair{a:0,b:0});
 }}
 let mut state=0x1234567812345678u64;
 for n in [0,1,2,3,4,7,8,15,16,31,32,63,64,127,128,1024,1736,1768] {for _ in 0..16 {
  let a:Vec<u8>=(0..n).map(|_|random(&mut state) as u8).collect();checks+=differential(&a,0);checks+=realloc_compare(&a);
  let a:Vec<u32>=(0..n).map(|_|random(&mut state) as u32).collect();checks+=differential(&a,0);
  let a:Vec<u64>=(0..n).map(|_|random(&mut state)).collect();checks+=differential(&a,0);
  let a:Vec<[u8;32]>=(0..n).map(|_|{let mut x=[0;32];for b in &mut x{*b=random(&mut state) as u8;}x}).collect();checks+=differential(&a,[0;32]);
  let a:Vec<Pair>=(0..n).map(|_|Pair{a:random(&mut state) as u32,b:random(&mut state) as u32}).collect();checks+=differential(&a,Pair{a:0,b:0});
 }}
 println!("KMX_NATIVE_PASS checks={checks} seed=0x1234567812345678 exhaustive_u32_alphabet=0,1,255,256,512 max_exhaustive_len=6 random_trials_per_type_len=16");
}
