//! Source-only emitter for the finite R748 point-1 basis leaves.
//!
//! This program deliberately uses only `std`.  It reads the R748 plan, checks
//! its pinned source files with its local SHA-256 implementation, and emits at
//! most 32 named sourcePointBasis lemmas per Lean file.  It never evaluates a
//! sourceChord, a matrix, or a witness relation.
use std::{env, fs, path::{Path, PathBuf}};

const MODULUS: u64 = 2_147_483_647;
const P: [i64; 10] = [1, 1, 2, 3, 4, 2, 2, 3, 2, -1];
const PINS: [(&str, &str); 5] = [
 ("docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/T163SourceTable.lean", "6aaf8bc2e1fce9a5a0116eac8eda44b5ca2032e5dcb5d2824587e05bf8ff3795"),
 ("docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/TwoSwapSourceTable.lean", "88bedf159e0cf288d514f59c734e8af6f6c42252c9875e02d67d330a0eaa87e7"),
 ("docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R746SelectedJointMinor.lean", "f2f1623052e035a0d9a8d6e635df38a9cfd3ee7177b84255a1f7065ea60ee399"),
 ("docs/research/v8-full-view-zk-20260912/lean/AspisV8R17/IndexSchedule.lean", "363b0eb4491d3cb40ad5d097e5e7f0242677f43808a1839bafe80add2356cfcf"),
 ("docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R748JointWitnessPointEntry.lean", "06dafa57a87f421dff2014f34f5f809cebf2cd418958e582b137451a43fe7276"),
];

fn sha256(bytes: &[u8]) -> String {
    const K: [u32; 64] = [
      0x428a2f98,0x71374491,0xb5c0fbcf,0xe9b5dba5,0x3956c25b,0x59f111f1,0x923f82a4,0xab1c5ed5,
      0xd807aa98,0x12835b01,0x243185be,0x550c7dc3,0x72be5d74,0x80deb1fe,0x9bdc06a7,0xc19bf174,
      0xe49b69c1,0xefbe4786,0x0fc19dc6,0x240ca1cc,0x2de92c6f,0x4a7484aa,0x5cb0a9dc,0x76f988da,
      0x983e5152,0xa831c66d,0xb00327c8,0xbf597fc7,0xc6e00bf3,0xd5a79147,0x06ca6351,0x14292967,
      0x27b70a85,0x2e1b2138,0x4d2c6dfc,0x53380d13,0x650a7354,0x766a0abb,0x81c2c92e,0x92722c85,
      0xa2bfe8a1,0xa81a664b,0xc24b8b70,0xc76c51a3,0xd192e819,0xd6990624,0xf40e3585,0x106aa070,
      0x19a4c116,0x1e376c08,0x2748774c,0x34b0bcb5,0x391c0cb3,0x4ed8aa4a,0x5b9cca4f,0x682e6ff3,
      0x748f82ee,0x78a5636f,0x84c87814,0x8cc70208,0x90befffa,0xa4506ceb,0xbef9a3f7,0xc67178f2];
    let mut m=bytes.to_vec(); let bits=(m.len() as u64)*8; m.push(0x80);
    while m.len()%64 != 56 { m.push(0); }
    m.extend_from_slice(&bits.to_be_bytes());
    let mut h=[0x6a09e667u32,0xbb67ae85,0x3c6ef372,0xa54ff53a,0x510e527f,0x9b05688c,0x1f83d9ab,0x5be0cd19];
    for c in m.chunks_exact(64) {
      let mut w=[0u32;64];
      for i in 0..16 { w[i]=u32::from_be_bytes(c[4*i..4*i+4].try_into().unwrap()); }
      for i in 16..64 { let s0=w[i-15].rotate_right(7)^w[i-15].rotate_right(18)^(w[i-15]>>3); let s1=w[i-2].rotate_right(17)^w[i-2].rotate_right(19)^(w[i-2]>>10); w[i]=w[i-16].wrapping_add(s0).wrapping_add(w[i-7]).wrapping_add(s1); }
      let(mut a,mut b,mut c0,mut d,mut e,mut f,mut g,mut hh)=(h[0],h[1],h[2],h[3],h[4],h[5],h[6],h[7]);
      for i in 0..64 { let s1=e.rotate_right(6)^e.rotate_right(11)^e.rotate_right(25); let ch=(e&f)^((!e)&g); let t1=hh.wrapping_add(s1).wrapping_add(ch).wrapping_add(K[i]).wrapping_add(w[i]); let s0=a.rotate_right(2)^a.rotate_right(13)^a.rotate_right(22); let maj=(a&b)^(a&c0)^(b&c0); let t2=s0.wrapping_add(maj); hh=g;g=f;f=e;e=d.wrapping_add(t1);d=c0;c0=b;b=a;a=t1.wrapping_add(t2); }
      h[0]=h[0].wrapping_add(a);h[1]=h[1].wrapping_add(b);h[2]=h[2].wrapping_add(c0);h[3]=h[3].wrapping_add(d);h[4]=h[4].wrapping_add(e);h[5]=h[5].wrapping_add(f);h[6]=h[6].wrapping_add(g);h[7]=h[7].wrapping_add(hh);
    }
    h.iter().map(|x|format!("{x:08x}")).collect()
}
fn required(a: &[String], name: &str) -> String { a.windows(2).find(|x|x[0]==name).map(|x|x[1].clone()).unwrap_or_else(||panic!("missing {name}")) }
fn array_after<'a>(s: &'a str, key: &str) -> &'a str { let p=s.find(key).expect("missing plan key"); let a=s[p..].find('[').unwrap()+p; let b=s[a..].find(']').unwrap()+a; &s[a+1..b] }
fn parse_indices(plan: &str) -> Vec<u32> { array_after(plan,"basis_guard_nonzero_original_indices").split(',').filter_map(|x|x.trim().parse().ok()).collect() }
fn basis(i:u32)->u64 { P.iter().enumerate().fold(1u64,|acc,(coord,&p)| { let bit=(i>>(9-coord))&1; let v=if bit==0 { (1-p).rem_euclid(MODULUS as i64) as u64 } else { p.rem_euclid(MODULUS as i64) as u64 }; acc*v%MODULUS }) }
fn factors(i:u32)->String { (0..10).map(|coord| { let bit=(i>>(9-coord))&1; let v=if bit==0 {1-P[coord]}else{P[coord]}; v.to_string() }).collect::<Vec<_>>().join(" * ") }
fn render_chunk(chunk:usize, xs:&[u32]) -> (String, String) {
 let name=format!("R753Point1BasisChunk{chunk:02}.lean");
 let mut s=String::new();
 s.push_str("import AspisV8R19.R748JointWitnessPointEntry\n\n");
 s.push_str("/-! Generated finite point-1 basis values. Each lemma reduces exactly ten source factors; R754 separately supplies the shared pivot 1023. -/\n");
 s.push_str("namespace AspisV8R19.R753Point1BasisValues\nopen AspisV8R16 AspisV8R17 AspisR19\nopen AspisV8R19.R748JointWitnessPointEntry\nnoncomputable section\n");
 for &i in xs {
   let v=basis(i);
   s.push_str(&format!("\n/-- index {i}; ten factors: {} -/\nlemma point1_basis_{i} : sourcePointBasis point {i} = ({v}:M) := by\n  rw [point_eq_p]\n  norm_num [sourcePointBasis, sourceMultilinearFactors, Fin.prod_univ_succ, p] <;> decide\n#print axioms point1_basis_{i}\n",factors(i)));
 }
 s.push_str("\nend\nend AspisV8R19.R753Point1BasisValues\n");
 (name,s)
}
fn render_manifest(plan_sha:&str, rev:&str, chunks:usize)->String {
 format!("plan_sha256={plan_sha}\nsource_revision={rev}\nindices=196\nchunks={chunks}\npivot=1023\npivot_proof=AspisR19.R754Point1GuardedTransport.point1_pivot_basis\npivot_neg_proof=AspisR19.R754Point1GuardedTransport.point1_pivot_basis_neg\nr754_source_sha256=f7af56ed8c49709ed749747f26f5d955b4e89ea1487f36043125f5dcdee3e7d0\n")
}
fn write_or_check(mode:&str, out:&Path, files:&[(String,String)]) {
 if mode=="--emit" {
   assert!(!out.exists(),"refuse to overwrite output directory");
   fs::create_dir_all(out).unwrap();
   for (name,text) in files { fs::write(out.join(name),text).unwrap(); }
 } else if mode=="--check" {
   assert!(out.is_dir(),"--check requires an existing output directory");
   let mut actual:Vec<String>=fs::read_dir(out).unwrap().map(|x|x.unwrap().file_name().into_string().unwrap()).collect();
   actual.sort(); let mut expected:Vec<String>=files.iter().map(|x|x.0.clone()).collect(); expected.sort();
   assert_eq!(actual,expected,"generated file set mismatch");
   for (name,text) in files { assert_eq!(fs::read(out.join(name)).unwrap(),text.as_bytes(),"generated text mismatch: {name}"); }
 } else { panic!("mode must be --emit or --check"); }
}
fn main() {
 let a:Vec<String>=env::args().collect();
 if a.len()!=12 { panic!("usage: (--emit|--check) --repo ROOT --plan PLAN --expected-plan-sha SHA --out-dir DIR --source-revision REV"); }
 let mode=&a[1]; let repo=PathBuf::from(required(&a,"--repo")); let plan_path=PathBuf::from(required(&a,"--plan")); let expected=required(&a,"--expected-plan-sha"); let out=PathBuf::from(required(&a,"--out-dir")); let rev=required(&a,"--source-revision");
 let plan=fs::read(&plan_path).unwrap(); let plan_sha=sha256(&plan); assert_eq!(plan_sha,expected,"plan SHA mismatch");
 let plan_text=String::from_utf8(plan).unwrap();
 for (rel,want) in PINS { assert_eq!(sha256(&fs::read(repo.join(rel)).unwrap()),want,"source pin mismatch: {rel}"); assert!(plan_text.contains(want),"plan lacks source pin {rel}"); }
 let xs=parse_indices(&plan_text); assert_eq!(xs.len(),196); assert!(xs.windows(2).all(|w|w[0]<w[1])); assert!(xs.iter().all(|&i|i>=768&&i<=1022));
 let mut files:Vec<(String,String)>=xs.chunks(32).enumerate().map(|(n,c)|render_chunk(n,c)).collect();
 files.push(("MANIFEST.txt".to_owned(),render_manifest(&plan_sha,&rev,(xs.len()+31)/32)));
 write_or_check(mode,&out,&files);
}
