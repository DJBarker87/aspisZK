import NDO_JGp_TX1Geometry
set_option autoImplicit false
namespace AspisR1.JGp_Seeds
open Aeneas Aeneas.Std Result

/-- Unused seed slots reject. The concrete installation supplies every source
operation used by the preparation/initial/pending/geometry witness. -/
def base : AspisR1CurrentCaller.Ops where
  op0 := fail .panic
  op1 := fun _ _ _=>fail .panic
  op2 := fun _=>fail .panic
  op3 := fun _=>fail .panic
  op4 := fun _=>fail .panic
  op5 := fun _ _ _=>fail .panic
  op6 := fun _ _ _ _ _ _=>fail .panic
  op7 := fun _ _ _ _ _ _ _ _=>fail .panic
  op8 := fun _ _ _ _ _=>fail .panic
  op9 := fun _ _ _ _ _=>fail .panic
  op10 := fun _ _=>fail .panic
  op11 := fun _ _=>fail .panic
  op12 := fail .panic
  op13 := fail .panic
  op14 := fail .panic
  op15 := fail .panic
  op16 := fun _ _ _ _ _ _=>fail .panic
  op17 := fun _ _=>fail .panic
  op18 := fun _=>fail .panic
  op19 := fun _ _ _=>fail .panic
  op20 := fun _=>fail .panic
  op21 := fail .panic

def query : Port3_NativeQueryBody.Ops where
  op0 := fun _ _ _=>fail .panic
  op1 := fun _=>fail .panic
  op2 := fun _ _=>fail .panic
  op3 := fun _ _=>fail .panic
  op4 := fail .panic
  op5 := fail .panic
  op6 := fun _ _=>fail .panic
  op7 := fun _ _=>fail .panic
  op8 := fun _=>fail .panic
  op9 := fun _ _=>fail .panic
  op10 := fun _=>fail .panic
  op11 := fun _ _=>fail .panic
  op12 := fun _ _=>fail .panic
  op13 := fun _ _=>fail .panic
  op14 := fun _ _ _ _=>fail .panic
  op15 := fun _ _ _=>fail .panic
  op16 := fun _ _ _=>fail .panic
  op17 := fun _ _ _=>fail .panic
  op18 := fun _ _=>fail .panic
  op19 := fun _ _=>fail .panic
  op20 := fun _ _=>fail .panic
  op21 := fun _ _=>fail .panic
  widePartialEq := {eq:=fun _ _=>fail .panic,ne:=fun _ _=>fail .panic}

def geometry : Port3_NativeGeometryBody.Ops Unit where
  op0 := fun _ _ _=>fail .panic
  op1 := fun _ _ _ _=>fail .panic
  op2 := fun _ _ _=>fail .panic
  op3 := fun _ _ _=>fail .panic
  op4 := fun _ _=>fail .panic
  op5 := fun _ _=>fail .panic
  op6 := fail .panic
  op7 := fail .panic
  op8 := fun _ _=>fail .panic
  op9 := fun _ _=>fail .panic
  op10 := fun _=>fail .panic
  op11 := fun _=>fail .panic
  op12 := fun _=>fail .panic
  op13 := fun _=>fail .panic
  op14 := fun _=>fail .panic
  op15 := fun _=>fail .panic
  mapIterator := fun _ _=>{next:=fun _=>fail .panic}
end AspisR1.JGp_Seeds
