import R1Z.PV_CB_Op101Types
import R1Z.PV_CB_State
set_option autoImplicit false
namespace R1Z.PV_CB_Op101Transport
abbrev N := ProverRwFull.aspis_core.field.QM31
abbrev C := ProverRwFull.aspis_core.field.CM31
abbrev R := PV_CB_ShippedOp101.aspis_core.field.QM31
abbrev RC := PV_CB_ShippedOp101.aspis_core.field.CM31
def encodeC (x : C) : RC := ⟨x.a,x.b⟩
def decodeC (x : RC) : C := ⟨x.a,x.b⟩
def encode (x : N) : R := ⟨encodeC x.c0,encodeC x.c1⟩
def decode (x : R) : N := ⟨decodeC x.c0,decodeC x.c1⟩
theorem native_roundtrip (x : N) : decode (encode x) = x := by cases x; rfl
theorem extracted_roundtrip (x : R) : encode (decode x) = x := by cases x; rfl
#print axioms native_roundtrip
#print axioms extracted_roundtrip
end R1Z.PV_CB_Op101Transport
