import R1Z.PV_CB_Op109Types
import R1Z.ProverRwFullExternalFuns
set_option autoImplicit false
namespace R1Z.PV_CB_Op109Transport
abbrev N := ProverRwFull.aspis_core.field.QM31
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev R := PV_CB_ShippedOp109.aspis_core.field.QM31
abbrev RC := PV_CB_ShippedOp109.aspis_core.field.CM31
def encodeC (x : C) : RC := ⟨x.a,x.b⟩
def decodeC (x : RC) : C := ⟨x.a,x.b⟩
def encode (x : N) : R := ⟨encodeC x.c0,encodeC x.c1⟩
def decode (x : R) : N := ⟨decodeC x.c0,decodeC x.c1⟩
theorem native_roundtrip (x : N) : decode (encode x) = x := by cases x; rfl
theorem extracted_roundtrip (x : R) : encode (decode x) = x := by cases x; rfl
#print axioms native_roundtrip
#print axioms extracted_roundtrip
abbrev W := ProverRwFull.aspis_core.field.wide_exact.WideExact
abbrev RW := PV_CB_ShippedOp109.aspis_core.field.wide_exact.WideExact
def encodeW (x : W) : RW := ⟨encode x.c0,encode x.c1⟩
def decodeW (x : RW) : W := ⟨decode x.c0,decode x.c1⟩
theorem native_wide_roundtrip (x : W) : decodeW (encodeW x) = x := by cases x; rfl
theorem extracted_wide_roundtrip (x : RW) : encodeW (decodeW x) = x := by cases x; rfl
#print axioms native_wide_roundtrip
#print axioms extracted_wide_roundtrip
end R1Z.PV_CB_Op109Transport
