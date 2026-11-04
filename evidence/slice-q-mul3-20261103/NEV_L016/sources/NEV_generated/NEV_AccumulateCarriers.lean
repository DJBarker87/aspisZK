import NEV_AccumulateRaw.Types
import NBF_RowInstall
set_option autoImplicit false
noncomputable section
namespace NEV_AccumulateCarriers
open Aeneas Aeneas.Std Result
abbrev RawQ := NEV_AccumulateRaw.aspis_core.field.QM31
abbrev RawE := NEV_AccumulateRaw.aspis_core.field.wide_exact.WideExact
abbrev Q := NBF_RowInstall.Q
abbrev E := NBF_RowInstall.E

def toQ (x : RawQ) : Q := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def fromQ (x : Q) : RawQ := ⟨⟨x.c0.a,x.c0.b⟩,⟨x.c1.a,x.c1.b⟩⟩
def toE (x : RawE) : E := ⟨toQ x.c0,toQ x.c1⟩
def fromE (x : E) : RawE := ⟨fromQ x.c0,fromQ x.c1⟩
def mapArray {A B : Type} {n : Usize} (f : A → B) (a : Array A n) : Array B n :=
 ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩
def mapVec {A B : Type} (f : A → B) (a : alloc.vec.Vec A) : alloc.vec.Vec B :=
 ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩

def toVariant (v : NEV_AccumulateRaw.transport.Variant) : AspisR1Stage2.transport.Variant :=
 match v with | .S1 => .S1 | .S2 => .S2 | .D => .D
def fromVariant (v : AspisR1Stage2.transport.Variant) : NEV_AccumulateRaw.transport.Variant :=
 match v with | .S1 => .S1 | .S2 => .S2 | .D => .D

def toPoint (p : NEV_AccumulateRaw.aspis_core.circle.SecureCirclePoint) : AspisR1Stage2.aspis_core.circle.SecureCirclePoint :=
 ⟨toQ p.x,toQ p.y⟩
def fromPoint (p : AspisR1Stage2.aspis_core.circle.SecureCirclePoint) : NEV_AccumulateRaw.aspis_core.circle.SecureCirclePoint :=
 ⟨fromQ p.x,fromQ p.y⟩

def toPrepared (p : NEV_AccumulateRaw.Prepared) : AspisR1Stage2.verifier.Prepared :=
 ⟨toVariant p.variant,p.roots,toE p.gamma,toE p.kappa,mapArray toE p.alpha,
 toQ p.rho,p.queries,mapArray toQ p.semantic_alpha,mapArray toPoint p.z,toE p.claim,p.state⟩
def fromPrepared (p : AspisR1Stage2.verifier.Prepared) : NEV_AccumulateRaw.Prepared :=
 ⟨fromVariant p.variant,p.roots,fromE p.gamma,fromE p.kappa,mapArray fromE p.alpha,
 fromQ p.rho,p.queries,mapArray fromQ p.semantic_alpha,mapArray fromPoint p.z,fromE p.claim,p.state⟩

def toAccumulator (a : NEV_AccumulateRaw.Accumulator) : AspisR1Stage2.verifier.Accumulator :=
 ⟨mapVec toQ a.weights,toE a.rhs,toQ a.power,a.next⟩
def fromAccumulator (a : AspisR1Stage2.verifier.Accumulator) : NEV_AccumulateRaw.Accumulator :=
 ⟨mapVec fromQ a.weights,fromE a.rhs,fromQ a.power,a.next⟩
def toWeights (b : NEV_AccumulateRaw.BatchedWeights) : AspisR1Stage2.verifier.BatchedWeights :=
 ⟨b.raw,b.terms⟩
def fromWeights (b : AspisR1Stage2.verifier.BatchedWeights) : NEV_AccumulateRaw.BatchedWeights :=
 ⟨b.raw,b.terms⟩

theorem q_roundtrip (x : RawQ) : fromQ (toQ x)=x := by cases x;rfl
theorem q_reverse (x : Q) : toQ (fromQ x)=x := by cases x;rfl
theorem e_roundtrip (x : RawE) : fromE (toE x)=x := by cases x;rfl
theorem e_reverse (x : E) : toE (fromE x)=x := by cases x;rfl
theorem weights_roundtrip (b : NEV_AccumulateRaw.BatchedWeights) : fromWeights (toWeights b)=b := by cases b;rfl
theorem weights_reverse (b : AspisR1Stage2.verifier.BatchedWeights) : toWeights (fromWeights b)=b := by cases b;rfl

/-- These are lossless maps of all fields, including fields not inspected by
this helper. No prepared-state projection is used as the output carrier. -/
theorem array_inverse {A B : Type} {n : Usize} (f : A → B) (g : B → A)
    (inverse : ∀ a,g (f a)=a) (a : Array A n) : mapArray g (mapArray f a)=a := by
  apply Subtype.ext
  change (a.val.map f).map g=a.val
  rw [List.map_map]
  simp only [Function.comp_def,inverse,List.map_id]
theorem vector_inverse {A B : Type} (f : A → B) (g : B → A)
    (inverse : ∀ a,g (f a)=a) (a : alloc.vec.Vec A) : mapVec g (mapVec f a)=a := by
  apply Subtype.ext
  change (a.val.map f).map g=a.val
  rw [List.map_map]
  simp only [Function.comp_def,inverse,List.map_id]
theorem point_roundtrip (p : NEV_AccumulateRaw.aspis_core.circle.SecureCirclePoint) :
    fromPoint (toPoint p)=p := by cases p;rfl
theorem point_reverse (p : AspisR1Stage2.aspis_core.circle.SecureCirclePoint) :
    toPoint (fromPoint p)=p := by cases p;rfl
theorem prepared_roundtrip (p : NEV_AccumulateRaw.Prepared) : fromPrepared (toPrepared p)=p := by
  cases p with
  | mk variant roots gamma kappa alpha rho queries semantic_alpha z claim state =>
    cases variant <;>
      simp only [toPrepared,fromPrepared,toVariant,fromVariant,e_roundtrip,q_roundtrip,
        array_inverse toE fromE e_roundtrip,array_inverse toQ fromQ q_roundtrip,
        array_inverse toPoint fromPoint point_roundtrip]
theorem prepared_reverse (p : AspisR1Stage2.verifier.Prepared) : toPrepared (fromPrepared p)=p := by
  cases p with
  | mk variant roots gamma kappa alpha rho queries semantic_alpha z claim state =>
    cases variant <;>
      simp only [toPrepared,fromPrepared,toVariant,fromVariant,e_reverse,q_reverse,
        array_inverse fromE toE e_reverse,array_inverse fromQ toQ q_reverse,
        array_inverse fromPoint toPoint point_reverse]
theorem accumulator_roundtrip (a : NEV_AccumulateRaw.Accumulator) : fromAccumulator (toAccumulator a)=a := by
  cases a
  simp only [toAccumulator,fromAccumulator,e_roundtrip,q_roundtrip,
    vector_inverse toQ fromQ q_roundtrip]
theorem accumulator_reverse (a : AspisR1Stage2.verifier.Accumulator) : toAccumulator (fromAccumulator a)=a := by
  cases a
  simp only [toAccumulator,fromAccumulator,e_reverse,q_reverse,
    vector_inverse fromQ toQ q_reverse]
#print axioms array_inverse
#print axioms vector_inverse
#print axioms point_roundtrip
#print axioms point_reverse
#print axioms prepared_roundtrip
#print axioms prepared_reverse
#print axioms accumulator_roundtrip
#print axioms accumulator_reverse

#print axioms q_roundtrip
#print axioms q_reverse
#print axioms e_roundtrip
#print axioms e_reverse
#print axioms weights_roundtrip
#print axioms weights_reverse
end NEV_AccumulateCarriers
end
