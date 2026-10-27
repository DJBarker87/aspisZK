import XRk_DecodeModels
open Aeneas Aeneas.Std Result ControlFlow Error
open XRk_Release XRk_FieldExternal
/- Exact wrapping arithmetic for canonical::Q::raw, fast_pairing.rs:88-101.
   Each operation wraps at u64 exactly as the owned reference. P6 OPEN. -/
def XRk_wrap64 (n : Nat) : Nat := n % 18446744073709551616
def XRk_sub64 (a b : Nat) : Nat := XRk_wrap64 (a + 18446744073709551616 - b)
def XRk_partial (n : Nat) : Nat := XRk_wrap64 (n % 2147483648 + n/2147483648)
def XRk_raw (x y : fast_pairing.canonical.Q) : List Nat :=
  let a := (x.val[0]?.getD 0#u32).val; let b := (x.val[1]?.getD 0#u32).val
  let c := (x.val[2]?.getD 0#u32).val; let d := (x.val[3]?.getD 0#u32).val
  let e := (y.val[0]?.getD 0#u32).val; let f := (y.val[1]?.getD 0#u32).val
  let g := (y.val[2]?.getD 0#u32).val; let h := (y.val[3]?.getD 0#u32).val
  let pp := 2147483647*2147483647
  let u := XRk_partial (XRk_sub64 (XRk_wrap64 (c*g+pp)) (d*h))
  let v := XRk_partial (XRk_wrap64 (c*h+d*g))
  [XRk_sub64 (XRk_wrap64 (XRk_sub64 (XRk_wrap64 (a*e+pp)) (b*f)+2*u+3*2147483647)) v,
   XRk_wrap64 (a*f+b*e+u+2*v),
   XRk_sub64 (XRk_sub64 (XRk_wrap64 (a*g+c*e+2*pp)) (b*h)) (d*f),
   XRk_wrap64 (a*h+b*g+c*f+d*e)]
def XRk_u64 (n : Nat) : U64 := UScalar.ofNat (XRk_wrap64 n) (by change _ ≤ 18446744073709551615; unfold XRk_wrap64; omega)
/- XRg_dot_reference: four independent folded wrapping sum updates. P6 OPEN. -/
def fast_pairing.canonical.Dot.push (s : fast_pairing.canonical.Dot) (a b : fast_pairing.canonical.Q) :
    Result fast_pairing.canonical.Dot :=
  let raw := XRk_raw a b
  let xs := (List.range 4).map fun i => XRk_u64
    ((s.sums.val[i]?.getD 0#u64).val + XRk_partial (raw[i]?.getD 0))
  if h : xs.length = 4 then ok ⟨⟨xs,h⟩⟩ else fail .panic

def XRk_dotFinish (d : fast_pairing.canonical.Dot) : Result aspis_core.field.QM31 := do
  let xs ← d.sums.val.mapM aspis_core.field.M31.reduce_u64
  ok (XRk_q xs)
def XRk_usize (n : Nat) : Usize := UScalar.ofNat (n % (UScalar.cMax .Usize+1)) (by have := Nat.mod_lt n (Nat.succ_pos (UScalar.cMax .Usize)); omega)
def XRk_toQ (q : aspis_core.field.QM31) : fast_pairing.canonical.Q :=
  Array.make 4#usize [q.c0.a,q.c0.b,q.c1.a,q.c1.b]
def XRk_dotZero : fast_pairing.canonical.Dot := ⟨Array.make 4#usize [0#u64,0#u64,0#u64,0#u64]⟩
def XRk_powers (x : XRk_Wide) : Nat → XRk_Wide → Result (List XRk_Wide)
  | 0,_ => ok []
  | 1,p => ok [p]
  | n+2,p => do
    let next ← aspis_core.field.wide_exact.WideExact.mul p x
    let rest ← XRk_powers x (n+1) next
    ok (p::rest)
def XRk_preparedPart {H : Type} (sem : r1_semantic.Verified H) (y1 : Slice U8)
    (g : Array XRk_Wide 29#usize) (point : Nat) : Result (Option XRk_Wide) := do
  let state ← (List.range 29).foldlM (fun (state : Option (fast_pairing.canonical.Dot × fast_pairing.canonical.Dot)) l => do
    match state with
    | none => ok none
    | some (a,b) =>
      let scalar ← if point < 3 then do
          let row ← Array.index_usize sem.claims (XRk_usize point)
          Array.index_usize row (XRk_usize l)
        else if point = 3 then Array.index_usize sem.extra (XRk_usize l)
        else if point = 4 then Array.index_usize sem.before_z1 (XRk_usize l)
        else do
          let bytes ← XRk_sliceRange y1 (32*l) (32*l+32)
          let e ← aspis_core.field.wide_exact.WideExact.from_le_bytes bytes
          match e with
          | some e => ok (newQ e.c0)
          | none => fail .panic
      if !(scalar.c0.a < 2147483647#u32 && scalar.c0.b < 2147483647#u32 && scalar.c1.a < 2147483647#u32 && scalar.c1.b < 2147483647#u32) then ok none
      else do
        let v ← Array.index_usize g (XRk_usize l)
        let a ← fast_pairing.canonical.Dot.push a (XRk_toQ (newQ v.c0)) (XRk_toQ scalar)
        let b ← fast_pairing.canonical.Dot.push b (XRk_toQ (newQ v.c1)) (XRk_toQ scalar)
        ok (some (a,b))) (some (XRk_dotZero,XRk_dotZero))
  match state with
  | none => ok none
  | some (a,b) => do
    let a ← XRk_dotFinish a
    let b ← XRk_dotFinish b
    ok (some (⟨oldQ a,oldQ b⟩ : XRk_Wide))
/- XRi_reference_prepared_claim: six scalar branches, 29 checked dot pushes,
   seven kappa powers and weighted parts; release trace is erased. P6 OPEN. -/
def verifier.prepared_claim {H : Type} (_ : aspis_core.digest.Digest32 H)
    (sem : r1_semantic.Verified H) (y1 : Slice U8) (inactive : XRk_Wide)
    (g : Array XRk_Wide 29#usize) (kappa : XRk_Wide) :
    Result (core.result.Result XRk_Wide verifier.Error) := do
  let one ← aspis_core.field.wide_exact.WideExact.ONE
  let zero ← aspis_core.field.wide_exact.WideExact.ZERO
  let powers ← XRk_powers kappa 7 one
  let parts ← (List.range 6).foldlM (fun (parts : Option (List XRk_Wide)) point => do
    match parts with
    | none => ok none
    | some parts =>
      let p ← XRk_preparedPart sem y1 g point
      ok (p.map (fun p => parts ++ [p]))) (some [])
  match parts with
  | none => ok (.Err .Parse)
  | some parts => do
    let parts := inactive :: parts
    let result ← (powers.zip parts).foldlM (fun sum (k,p) => do
      let term ← aspis_core.field.wide_exact.WideExact.mul k p
      aspis_core.field.wide_exact.WideExact.add sum term) zero
    ok (.Ok result)
