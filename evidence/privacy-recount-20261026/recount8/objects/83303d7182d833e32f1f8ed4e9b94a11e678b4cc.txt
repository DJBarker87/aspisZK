import R1Z.PV_Join_OwnedFuns5
import R1Z.PV_Join_Canonical5
import R1Z.ProverRwP6ArrayMap
set_option autoImplicit false
namespace R1Z.PV_Join_OwnedCarriers5
open Aeneas Aeneas.Std Result ProverRwFull PV_Join_Canonical5
abbrev OC := PV_Join_Direct5Source.aspis_core.field.CM31
abbrev OQ := PV_Join_Direct5Source.aspis_core.field.QM31
def encodeC (x : aspis_core.field.CM31) : OC := ⟨x.a,x.b⟩
def decodeC (x : OC) : aspis_core.field.CM31 := ⟨x.a,x.b⟩
def encodeQ (x : aspis_core.field.QM31) : OQ := ⟨encodeC x.c0,encodeC x.c1⟩
def decodeQ (x : OQ) : aspis_core.field.QM31 := ⟨decodeC x.c0,decodeC x.c1⟩
theorem decode_encodeC (x : aspis_core.field.CM31) : decodeC (encodeC x)=x := by cases x; rfl
theorem encode_decodeC (x : OC) : encodeC (decodeC x)=x := by cases x; rfl
theorem decode_encodeQ (x : aspis_core.field.QM31) : decodeQ (encodeQ x)=x := by cases x; rfl
theorem encode_decodeQ (x : OQ) : encodeQ (decodeQ x)=x := by cases x; rfl
abbrev encodeArray {n : Usize} := @ProverRwP6ArrayMap.map aspis_core.field.QM31 OQ n encodeQ
abbrev decodeArray {n : Usize} := @ProverRwP6ArrayMap.map OQ aspis_core.field.QM31 n decodeQ
theorem decode_encodeArray {n : Usize} (xs : Array aspis_core.field.QM31 n) :
    decodeArray (encodeArray xs)=xs := ProverRwP6ArrayMap.roundtrip _ _ decode_encodeQ xs

def owned (p : Array aspis_core.field.QM31 28#usize) (x : aspis_core.field.QM31) :
    Result aspis_core.field.QM31 := do
  let value ← PV_Join_Direct5Source.evaluate (encodeArray p) (encodeQ x)
  ok (decodeQ value)

/-- Exact owned-reference equation on arbitrary raw inputs. The canonical-domain
shipped/reference equality and deployed producer invariant are separate obligations. -/
theorem owned_equation (p : Array aspis_core.field.QM31 28#usize) (x : aspis_core.field.QM31) :
    owned p x = (do
      let value ← PV_Join_Direct5Source.evaluate (encodeArray p) (encodeQ x)
      ok (decodeQ value)) := rfl

#print axioms decode_encodeC
#print axioms encode_decodeC
#print axioms decode_encodeQ
#print axioms encode_decodeQ
#print axioms decode_encodeArray
#print axioms owned_equation
end R1Z.PV_Join_OwnedCarriers5
