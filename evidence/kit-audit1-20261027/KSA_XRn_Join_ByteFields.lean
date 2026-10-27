import KSA_XRn_Join_StdExtra

namespace KSA_Isolated
open Aeneas Aeneas.Std Result ControlFlow Error
open XRn_Join_Release XRn_Join_FieldExternal
/- Byte models of field.rs / wide_exact.rs. Canonical test precedes construction;
   exact shipped/reference P6 and allocator correspondence remain OPEN. -/
def XRn_Join_word (bs : List U8) : U32 :=
  UScalar.ofNat (XRn_Join_Bytes.le32 bs % 4294967296) (by change _ ≤ 4294967295; omega)
def XRn_Join_q (xs : List U32) : aspis_core.field.QM31 :=
  ⟨⟨xs[0]?.getD 0#u32,xs[1]?.getD 0#u32⟩,⟨xs[2]?.getD 0#u32,xs[3]?.getD 0#u32⟩⟩
def aspis_core.field.M31.from_le_bytes (bs : Array U8 4#usize) : Result (Option aspis_core.field.M31) :=
  let n := XRn_Join_word bs.val
  ok (if n < 2147483647#u32 then some n else none)
def aspis_core.field.QM31.from_le_bytes (bs : Slice U8) : Result (Option aspis_core.field.QM31) :=
  let xs := (List.range 4).map fun i => XRn_Join_word ((bs.val.drop (4*i)).take 4)
  ok (if bs.val.length = 16 ∧ xs.all (fun x => x < 2147483647#u32) then some (XRn_Join_q xs) else none)
def aspis_core.field.wide_exact.WideExact.from_limbs (xs : Array U32 8#usize) : Result (Option XRn_Join_Wide) :=
  ok (if xs.val.all (fun x => x < 2147483647#u32) then
    some ⟨oldQ (XRn_Join_q (xs.val.take 4)),oldQ (XRn_Join_q (xs.val.drop 4))⟩ else none)
def aspis_core.field.wide_exact.WideExact.to_limbs (x : XRn_Join_Wide) : Result (Array U32 8#usize) :=
  let a := newQ x.c0; let b := newQ x.c1
  ok (Array.make 8#usize [a.c0.a,a.c0.b,a.c1.a,a.c1.b,b.c0.a,b.c0.b,b.c1.a,b.c1.b])
def aspis_core.field.wide_exact.WideExact.from_le_bytes (bs : Slice U8) : Result (Option XRn_Join_Wide) :=
  let xs := (List.range 8).map fun i => XRn_Join_word ((bs.val.drop (4*i)).take 4)
  ok (if bs.val.length = 32 ∧ xs.all (fun x => x < 2147483647#u32) then
    some ⟨oldQ (XRn_Join_q (xs.take 4)),oldQ (XRn_Join_q (xs.drop 4))⟩ else none)
def XRn_Join_wordBytes (x : U32) : List U8 :=
  (List.range 4).map fun i => UScalar.ofNat (x.val / 256^i % 256) (by change _ ≤ 255; omega)
def XRn_Join_qBytes (x : aspis_core.field.QM31) : List U8 :=
  [x.c0.a,x.c0.b,x.c1.a,x.c1.b].flatMap XRn_Join_wordBytes
def aspis_core.field.wide_exact.WideExact.to_le_bytes (x : XRn_Join_Wide) : Result (Array U8 32#usize) :=
  let bs := XRn_Join_qBytes (newQ x.c0) ++ XRn_Join_qBytes (newQ x.c1)
  if h : bs.length = 32 then ok ⟨bs,h⟩ else fail .panic
def aspis_core.field.wide_exact.WideExact.Insts.Aspis_coreR0ScalarCodeField.from_m31
    (x : aspis_core.field.M31) : Result XRn_Join_Wide :=
  aspis_core.field.wide_exact.WideExact.from_qm31 ⟨⟨x,0#u32⟩,⟨0#u32,0#u32⟩⟩
/- Square-and-multiply model of the source exponentiation: inv panics on zero. -/
def XRn_Join_mpow (x : aspis_core.field.M31) : Nat → Result aspis_core.field.M31
  | 0 => ok 1#u32
  | n+1 => do
    let y ← XRn_Join_mpow x (n/2)
    let z ← aspis_core.field.M31.mul y y
    if n%2 = 0 then aspis_core.field.M31.mul z x else ok z
termination_by n => n
def aspis_core.field.M31.inv (x : aspis_core.field.M31) : Result aspis_core.field.M31 :=
  if x = 0#u32 then fail .panic else XRn_Join_mpow x 2147483645

def aspis_core.r0.domain.FibreIndex.new (x : Usize) :
    Result (core.result.Result aspis_core.r0.domain.FibreIndex aspis_core.r0.Error) :=
  ok (if x < 262144#usize then .Ok x else .Err .IndexOutOfRange)
def aspis_core.r0.domain.FibreIndex.get (x : aspis_core.r0.domain.FibreIndex) : Result Usize := ok x
def aspis_core.circle.SecureCirclePoint.Insts.CoreCmpPartialEqSecureCirclePoint.eq
    (a b : aspis_core.circle.SecureCirclePoint) : Result Bool :=
  ok (qeq a.x b.x && qeq a.y b.y)
def aspis_core.r0.merkle.C1_TAG : Result U8 := ok 113#u8
def aspis_core.r0.merkle.C2_TAG : Result U8 := ok 241#u8

end KSA_Isolated
