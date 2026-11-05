import NIL_ResultTransport
set_option autoImplicit false
noncomputable section
namespace NIL_StatePort
open Aeneas Aeneas.Std Result NIL_Carriers NIL_ResultTransport
namespace F
abbrev P := NID_ResumeEmission.verifier.Prepared
abbrev A := NID_ResumeEmission.verifier.Accumulator
abbrev Z := NID_ResumeEmission.aspis_core.circle.SecureCirclePoint
end F
namespace C
abbrev P := AspisR1Stage2.verifier.Prepared
abbrev A := AspisR1Stage2.verifier.Accumulator
abbrev Z := AspisR1Stage2.aspis_core.circle.SecureCirclePoint
end C

def point (x : F.Z) : C.Z := ⟨k x.x,k x.y⟩
def unPoint (x : C.Z) : F.Z := ⟨unK x.x,unK x.y⟩
def prepared (p : F.P) : C.P :=
 ⟨variant p.variant,p.roots,e p.gamma,e p.kappa,array e p.alpha,k p.rho,p.queries,
 array k p.semantic_alpha,array point p.z,e p.claim,p.state⟩
def unPrepared (p : C.P) : F.P :=
 ⟨unVariant p.variant,p.roots,unE p.gamma,unE p.kappa,array unE p.alpha,unK p.rho,p.queries,
 array unK p.semantic_alpha,array unPoint p.z,unE p.claim,p.state⟩
def accumulator (a : F.A) : C.A := ⟨vec k a.weights,e a.rhs,k a.power,a.next⟩
def unAccumulator (a : C.A) : F.A := ⟨vec unK a.weights,unE a.rhs,unK a.power,a.next⟩
def pair (x : F.P × F.A) : C.P × C.A := (prepared x.1,accumulator x.2)
def unPair (x : C.P × C.A) : F.P × F.A := (unPrepared x.1,unAccumulator x.2)
def reply := outer (NIL_Carriers.inner pair)

theorem point_roundtrip (x : F.Z) : unPoint (point x)=x := by cases x;simp only [point,unPoint,k_roundtrip]
theorem point_reverse (x : C.Z) : point (unPoint x)=x := by cases x;simp only [point,unPoint,k_reverse]
theorem variant_reverse (x : Cohort.V) : variant (unVariant x)=x := by cases x <;> rfl

theorem prepared_roundtrip (p : F.P) : unPrepared (prepared p)=p := by
 cases p
 simp only [prepared,unPrepared,variant_roundtrip,e_roundtrip,k_roundtrip,
 array_roundtrip e unE e_roundtrip,array_roundtrip k unK k_roundtrip,
 array_roundtrip point unPoint point_roundtrip]

theorem prepared_reverse (p : C.P) : prepared (unPrepared p)=p := by
 cases p
 simp only [prepared,unPrepared,variant_reverse,e_reverse,k_reverse,
 array_roundtrip unE e e_reverse,array_roundtrip unK k k_reverse,
 array_roundtrip unPoint point point_reverse]

theorem accumulator_roundtrip (a : F.A) : unAccumulator (accumulator a)=a := by
 cases a
 simp only [accumulator,unAccumulator,e_roundtrip,k_roundtrip,vec_roundtrip k unK k_roundtrip]
theorem accumulator_reverse (a : C.A) : accumulator (unAccumulator a)=a := by
 cases a
 simp only [accumulator,unAccumulator,e_reverse,k_reverse,vec_roundtrip unK k k_reverse]
theorem pair_roundtrip (x : F.P × F.A) : unPair (pair x)=x := by
 cases x;simp only [pair,unPair,prepared_roundtrip,accumulator_roundtrip]
theorem pair_injective {x y : F.P × F.A} (h : pair x=pair y) : x=y := by
 have h' := congrArg unPair h
 simpa only [pair_roundtrip] using h'

theorem reply_injective {x y : Result (core.result.Result (F.P × F.A) Fresh.Err)}
 (h : reply x=reply y) : x=y := by
 apply outer_injective (NIL_Carriers.inner pair) (unInner unPair)
   (inner_roundtrip pair unPair pair_roundtrip) h

#print axioms point_roundtrip
#print axioms point_reverse
#print axioms variant_reverse
#print axioms prepared_roundtrip
#print axioms prepared_reverse
#print axioms accumulator_roundtrip
#print axioms accumulator_reverse
#print axioms pair_roundtrip
#print axioms pair_injective
#print axioms reply_injective
end NIL_StatePort
