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
const R755_PIN: (&str,&str) = ("docs/research/v8-full-view-zk-20260912/lean/AspisV8R19/R755Point1BasisTransport.lean", "360f0bb52c86dd99c09f38a80ece0e5b4886205f8d9e8c84dc760a8a044208ab");
const BASIS_FILES: [(&str,&str);7] = [
 ("R753Point1BasisChunk00.lean","ac803e04765580e7fb838c5df7653640897de816858031fbfd28c3ff15fe3590"),
 ("R753Point1BasisChunk01.lean","12a9ff1343e7323712222360b7c595df8ac638627b8b19b4673197c470f7cf1a"),
 ("R753Point1BasisChunk02.lean","96f58be2f6c50d45193914e41d0fb6ffc742b67d58c174b36b51b172ea0e69ae"),
 ("R753Point1BasisChunk03.lean","1b1d74aabadae53624554cffe132282f221b656cb02c4d5d0c1b2ea4d23bd435"),
 ("R753Point1BasisChunk04.lean","77c4eff1204852b867fab2bb4a1c5ce8dec2364fa59a06fa3aa51bbd0bb817eb"),
 ("R753Point1BasisChunk05.lean","369acf5ce92ff62cbc17ee76a9822b880d39f345890c7ca963e6984f8ffbaf9c"),
 ("R753Point1BasisChunk06.lean","00a16f7ecfc41c5b9d5b90db053dd6005886f4c22329ed34929f1cbffdf72991"),
];
#[derive(Clone)] struct Leaf { j:u32, original:u32, inactive:bool, basis:u64, basis_chunk:usize }
fn array_after<'a>(s:&'a str,key:&str)->&'a str { let p=s.find(key).expect("missing plan key"); let a=s[p..].find('[').unwrap()+p; let b=s[a..].find(']').unwrap()+a; &s[a+1..b] }
fn number_after(s:&str,key:&str)->u32 { s.find(key).and_then(|p|s[p+key.len()..].trim_start().split(|c:char|!c.is_ascii_digit()).next()).and_then(|x|x.parse().ok()).expect("missing number") }
fn bool_after(s:&str,key:&str)->bool { let p=s.find(key).expect("missing bool"); s[p+key.len()..].trim_start().starts_with("true") }
fn basis_values(dir:&Path)->std::collections::BTreeMap<u32,(u64,usize)> {
 let mut out=std::collections::BTreeMap::new();
 for (chunk,(name,want)) in BASIS_FILES.iter().enumerate() {
   let text=fs::read_to_string(dir.join(name)).unwrap(); assert_eq!(sha256(text.as_bytes()),*want,"basis source pin mismatch: {name}");
   for part in text.split("lemma point1_basis_").skip(1) {
     let i=part.split(':').next().unwrap().parse::<u32>().unwrap();
     let eq=part.find("= (").unwrap(); let rest=&part[eq+3..]; let b=rest.split(":M)").next().unwrap().parse::<u64>().unwrap();
     assert!(out.insert(i,(b,chunk)).is_none(),"duplicate basis index");
   }
 }
 assert_eq!(out.len(),196); out
}
fn leaves(plan:&str,bases:&std::collections::BTreeMap<u32,(u64,usize)>)->Vec<Leaf> {
 let mut out=Vec::new();
 for part in array_after(plan,"leaf_records").split('{').skip(1) {
   let j=number_after(part,"\"leaf\":"); let original=number_after(part,"\"original\":");
   let inactive=bool_after(part,"\"inactive\":"); let zero=bool_after(part,"\"basis_zero_by_p01\":");
   if !zero { let (basis,basis_chunk)=bases.get(&original).copied().expect("nonzero leaf absent from basis sources"); out.push(Leaf{j,original,inactive,basis,basis_chunk}); }
 }
 out.sort_by_key(|x|x.j); assert_eq!(out.len(),196); assert!(out.windows(2).all(|w|w[0].j<w[1].j)); assert!(out.iter().all(|x|x.original!=1023)); out
}
fn membership(o:u32, inactive:bool)->String {
 if inactive { format!("  have hmem : ({o} : Fin 1024) ∈ inactive.erase 1023 := by\n    change ({o} : Fin 1024) ∈ T163SourceTable.inactive.erase 1023\n    rw [Finset.mem_erase]\n    constructor\n    · decide\n    · rw [T163SourceTable.inactive, Finset.mem_filter]\n      exact ⟨Finset.mem_univ _, by decide⟩\n")
 } else { format!("  have hnotmem : ({o} : Fin 1024) ∉ inactive.erase 1023 := by\n    intro h\n    change ({o} : Fin 1024) ∈ T163SourceTable.inactive.erase 1023 at h\n    have hi : ({o} : Fin 1024) ∈ T163SourceTable.inactive := (Finset.mem_erase.mp h).2\n    change ({o} : Fin 1024) ∈ Finset.univ.filter (fun k => T163SourceTable.isInactive k) at hi\n    have hb : T163SourceTable.isInactive ({o} : Fin 1024) = true := (Finset.mem_filter.mp hi).2\n    have hf : T163SourceTable.isInactive ({o} : Fin 1024) = false := by decide\n    rw [hf] at hb\n    cases hb\n") }
}
fn render_chunk(chunk:usize,xs:&[Leaf])->(String,String) {
 let name=format!("R759Point1TransportChunk{chunk:02}.lean"); let mut used:Vec<usize>=xs.iter().map(|x|x.basis_chunk).collect(); used.sort(); used.dedup();
 let mut s=String::from("import AspisV8R19.R755Point1BasisTransport\n");
 for n in used { s.push_str(&format!("import AspisV8R19.R753Point1BasisChunk{n:02}\n")); }
 s.push_str("\nnamespace AspisR19.R759Point1TransportLeaves\nopen AspisV8R16 AspisV8R17 AspisR19\nopen AspisR19.TwoSwapSourceTable\nopen AspisR19.R755Point1BasisTransport\nopen AspisV8R19.R748JointWitnessPointEntry\nopen AspisV8R19.R753Point1BasisValues\nnoncomputable section\n");
 for x in xs { let rhs=if x.inactive {format!("({}:M) + 576",x.basis)}else{format!("({}:M)",x.basis)}; s.push_str(&format!("\n/-- finite transport leaf j={}, original={} -/\nlemma transport_leaf_{:04} : w {} = {} := by\n  let j : Fin 1024 := ⟨{}, by omega⟩\n  have horder : order j = ({} : Fin 1024) := by decide\n  have hb : sourcePointBasis point (order j).val = ({}:M) := by\n    rw [horder]\n    exact point1_basis_{}\n  have hw := w_from_basis j ({}:M) hb\n  rw [horder] at hw\n{}  simp only [if_{} {}] at hw\n  simpa [j] using hw\n#print axioms transport_leaf_{:04}\n",x.j,x.original,x.j,x.j,rhs,x.j,x.original,x.basis,x.original,x.basis,membership(x.original,x.inactive),if x.inactive{"pos"}else{"neg"},if x.inactive{"hmem"}else{"hnotmem"},x.j)); }
 s.push_str("\nend\nend AspisR19.R759Point1TransportLeaves\n"); (name,s)
}
fn manifest(plan_sha:&str,rev:&str)->String { format!("plan_sha256={plan_sha}\nsource_revision={rev}\nleaves=196\nchunks=7\nr755_source_sha256={}\nbasis_manifest_sha256={}\n",R755_PIN.1, "0cf6dfd060ed25cc0973ff2a77774e328783a5e3cfc71ec65077ce5153e31f61") }
fn write_or_check(mode:&str,out:&Path,files:&[(String,String)]) { if mode=="--emit" {assert!(!out.exists(),"refuse overwrite");fs::create_dir_all(out).unwrap();for(n,t)in files{fs::write(out.join(n),t).unwrap();}} else if mode=="--check" {assert!(out.is_dir(),"missing output");let mut a:Vec<_>=fs::read_dir(out).unwrap().map(|x|x.unwrap().file_name().into_string().unwrap()).collect();let mut e:Vec<_>=files.iter().map(|x|x.0.clone()).collect();a.sort();e.sort();assert_eq!(a,e,"file set mismatch");for(n,t)in files{assert_eq!(fs::read(out.join(n)).unwrap(),t.as_bytes(),"text mismatch: {n}");}}else{panic!("mode")}}
fn main(){let a:Vec<String>=env::args().collect();if a.len()!=14{panic!("usage: (--emit|--check) --repo ROOT --plan PLAN --basis-dir DIR --expected-plan-sha SHA --out-dir DIR --source-revision REV")};let mode=&a[1];let repo=PathBuf::from(required(&a,"--repo"));let plan_path=PathBuf::from(required(&a,"--plan"));let basis_dir=PathBuf::from(required(&a,"--basis-dir"));let expected=required(&a,"--expected-plan-sha");let out=PathBuf::from(required(&a,"--out-dir"));let rev=required(&a,"--source-revision");let plan=fs::read(&plan_path).unwrap();let plan_sha=sha256(&plan);assert_eq!(plan_sha,expected);let text=String::from_utf8(plan).unwrap();for(rel,want)in PINS{assert_eq!(sha256(&fs::read(repo.join(rel)).unwrap()),want,"source pin: {rel}");assert!(text.contains(want))};assert_eq!(sha256(&fs::read(repo.join(R755_PIN.0)).unwrap()),R755_PIN.1);let b=basis_values(&basis_dir);let leaves=leaves(&text,&b);let mut files:Vec<_>=leaves.chunks(32).enumerate().map(|(n,c)|render_chunk(n,c)).collect();files.push(("MANIFEST.txt".into(),manifest(&plan_sha,&rev)));write_or_check(mode,&out,&files)}
