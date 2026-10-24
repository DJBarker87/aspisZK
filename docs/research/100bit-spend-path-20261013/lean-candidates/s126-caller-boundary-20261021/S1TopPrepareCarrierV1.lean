import S6CurrentVerifierCarrierV1
import VTop_Model
import CurrentPreparedClaimCarriers
set_option autoImplicit false
namespace AspisS1TopPrepareCarrier
open Aeneas Aeneas.Std Result
open AspisR1ClaimPreparedBridge
namespace Current
abbrev K := AspisR1CurrentCaller.aspis_core.field.QM31
abbrev E := AspisR1CurrentCaller.aspis_core.field.wide_exact.WideExact
abbrev Point := AspisR1CurrentCaller.aspis_core.circle.SecureCirclePoint
abbrev Prepared := AspisR1CurrentCaller.verifier.Prepared
abbrev Variant := AspisR1CurrentCaller.transport.Variant
end Current
namespace Top
abbrev K := VTop_Stages.aspis_core.field.QM31
abbrev E := VTop_Stages.aspis_core.field.wide_exact.WideExact
abbrev Point := VTop_Stages.aspis_core.circle.SecureCirclePoint
abbrev Prepared := VTop_Stages.verifier.Prepared
abbrev Variant := VTop_Stages.transport.Variant
end Top

def toK (x : Current.K) : Top.K :=
  {c0:={a:=x.c0.a,b:=x.c0.b},c1:={a:=x.c1.a,b:=x.c1.b}}
def fromK (x : Top.K) : Current.K :=
  {c0:={a:=x.c0.a,b:=x.c0.b},c1:={a:=x.c1.a,b:=x.c1.b}}
def toE (x : Current.E) : Top.E := {c0:=toK x.c0,c1:=toK x.c1}
def fromE (x : Top.E) : Current.E := {c0:=fromK x.c0,c1:=fromK x.c1}
def toPoint (x : Current.Point) : Top.Point := {x:=toK x.x,y:=toK x.y}
def fromPoint (x : Top.Point) : Current.Point := {x:=fromK x.x,y:=fromK x.y}
def toVariant : Current.Variant → Top.Variant | .S1 => .S1 | .S2 => .S2 | .D => .D
def fromVariant : Top.Variant → Current.Variant | .S1 => .S1 | .S2 => .S2 | .D => .D

@[simp] theorem k_round (x : Current.K) : fromK (toK x)=x := rfl
@[simp] theorem k_back (x : Top.K) : toK (fromK x)=x := rfl
@[simp] theorem e_round (x : Current.E) : fromE (toE x)=x := rfl
@[simp] theorem e_back (x : Top.E) : toE (fromE x)=x := rfl
@[simp] theorem point_round (x : Current.Point) : fromPoint (toPoint x)=x := rfl
@[simp] theorem point_back (x : Top.Point) : toPoint (fromPoint x)=x := rfl
@[simp] theorem variant_round (x : Current.Variant) : fromVariant (toVariant x)=x := by cases x <;> rfl
@[simp] theorem variant_back (x : Top.Variant) : toVariant (fromVariant x)=x := by cases x <;> rfl

/-- Full value-carrier transport. Every Prepared field is retained. This is a
logical ABI bijection, not a runtime copy, native-call premise or reduced token. -/
def toPrepared (p : Current.Prepared) : Top.Prepared :=
  {variant:=toVariant p.variant,roots:=p.roots,gamma:=toE p.gamma,kappa:=toE p.kappa,
   alpha:=mapArray toE p.alpha,rho:=toK p.rho,queries:=p.queries,
   semantic_alpha:=mapArray toK p.semantic_alpha,z:=mapArray toPoint p.z,
   claim:=toE p.claim,state:=p.state}
def fromPrepared (p : Top.Prepared) : Current.Prepared :=
  {variant:=fromVariant p.variant,roots:=p.roots,gamma:=fromE p.gamma,kappa:=fromE p.kappa,
   alpha:=mapArray fromE p.alpha,rho:=fromK p.rho,queries:=p.queries,
   semantic_alpha:=mapArray fromK p.semantic_alpha,z:=mapArray fromPoint p.z,
   claim:=fromE p.claim,state:=p.state}

@[simp] theorem prepared_round (p : Current.Prepared) : fromPrepared (toPrepared p)=p := by
  cases p
  simp only [fromPrepared,toPrepared,k_round,e_round,variant_round,
    mapArray_inverse toE fromE e_round,mapArray_inverse toK fromK k_round,
    mapArray_inverse toPoint fromPoint point_round]
@[simp] theorem prepared_back (p : Top.Prepared) : toPrepared (fromPrepared p)=p := by
  cases p
  simp only [fromPrepared,toPrepared,k_back,e_back,variant_back,
    mapArray_inverse fromE toE e_back,mapArray_inverse fromK toK k_back,
    mapArray_inverse fromPoint toPoint point_back]

def preparedEquiv : Current.Prepared ≃ Top.Prepared :=
  ⟨toPrepared,fromPrepared,prepared_round,prepared_back⟩

#print axioms prepared_round
#print axioms prepared_back
#print axioms preparedEquiv
end AspisS1TopPrepareCarrier
