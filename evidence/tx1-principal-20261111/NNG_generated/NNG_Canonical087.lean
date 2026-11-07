import RSL_TX1_087
set_option autoImplicit false
namespace AspisR1.NNG_Canonical087
open RSL

def observed (V : VLib) (a : TX1_087.Args V) (v : V.View) : RE V.VErr (Verified V × V.View) :=
 RE.bind (RE.mapErr (fun _=>V.vSemantic)
  (Spec.call (TX1_137.Domain V) (TX1_137.Ref V) ⟨a.public_,V.viewSemantic v⟩)) fun sem=>RE.pure (sem,v)
def view (V : VLib) (a : TX1_087.Args V) (semantic y1 : Bytes) : RE V.VErr (Verified V × V.View) :=
 RE.bind (V.wideView.run (a.proof,semantic,y1)) fun v=>observed V a v
def values (V : VLib) (a : TX1_087.Args V) (semantic y10 : Bytes) : RE V.VErr (Verified V × V.View) :=
 RE.bind (RE.mapErr V.codecToV (V.expandValues.run (slice a.proof OFF_Y1 OFF_INACTIVE,y10))) fun y1=>view V a semantic y1
def semantic (V : VLib) (a : TX1_087.Args V) (semantic0 y10 : Bytes) : RE V.VErr (Verified V × V.View) :=
 RE.bind (RE.mapErr V.codecToV (V.expandSemantic.run (slice a.proof OFF_SEMANTIC OFF_Y1,semantic0))) fun sem=>values V a sem y10
def front (V : VLib) (a : TX1_087.Args V) : RE V.VErr (Verified V × V.View) :=
 RE.bind (RE.mapErr (fun _=>V.vAllocation) (V.filled.run (LOGICAL_SEMANTIC+LOGICAL_Y1))) fun logical=>
 semantic V a (logical.take LOGICAL_SEMANTIC) (logical.drop LOGICAL_SEMANTIC)
theorem front_ref (V : VLib) (a : TX1_087.Args V) : front V a=TX1_087.front V a := rfl
#print axioms front_ref
end AspisR1.NNG_Canonical087
