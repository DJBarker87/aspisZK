
// Verification-only raw Rust representation for checked contract havoc.
// Its caller must apply the verified canonical postcondition before arithmetic.
#[cfg(kani)]
impl kani::Arbitrary for WideExact {
 fn any()->Self{
  let [a,b,c,d,e,f,g,h]=kani::any::<[u32;8]>();
  Self{c0:QM31{c0:CM31{a:M31(a),b:M31(b)},c1:CM31{a:M31(c),b:M31(d)}},
       c1:QM31{c0:CM31{a:M31(e),b:M31(f)},c1:CM31{a:M31(g),b:M31(h)}}}
 }
}
