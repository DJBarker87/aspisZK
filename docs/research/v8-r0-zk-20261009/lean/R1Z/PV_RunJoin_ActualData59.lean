import R1Z.PV_RunJoin_ActualRunSources59
import R1Z.PV_RunJoin_BackendRawCoefficients58
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_ActualData59
open Aeneas Aeneas.Std Result ProverRwFull
open PV_RunJoin_NativeControl55 (Phase)
open ProverCommitPrimitive47 ProverCommitWideOps48
open ProverCommitValueRange47 (embed)
open AspisR1.ExtractedCurrentQM31Exact (decode)
variable [ExternalTypes] [ExternalFuns]
attribute [local instance] Classical.propDecidable

def zeroQ : aspis_core.field.QM31 := ⟨⟨0#u32,0#u32⟩,⟨0#u32,0#u32⟩⟩
def zeroW : aspis_core.field.wide_exact.WideExact := ⟨zeroQ,zeroQ⟩

def rawW (w : aspis_core.field.wide_exact.WideExact) : Raw :=
  (PV_RunJoin_SemanticScalar50.raw w.c0,PV_RunJoin_SemanticScalar50.raw w.c1)

/-- Read the returned stored semantic columns. Indexing is a symbolic list
projection; normalization reflects the actual embedding constructors. -/
def coefficients (p : Phase) (l j : Nat) : Old.Q :=
  ProverCommitNativeOps47.normalize (PV_RunJoin_SemanticScalar50.raw
    (((p.sem.columns.val[l]?).map (fun c => c.val[j]?.getD zeroQ)).getD zeroQ))

def preparedField (p : Phase)
    (field : prover.PreparedOpening → aspis_core.field.wide_exact.WideExact) : Raw :=
  rawW (match PV_RunJoin_ActualRunSources59.prepare p with
    | .ok (.Ok prepared) => field prepared
    | _ => zeroW)

def finalScalar (p : Phase) : Raw := rawW
  (match PV_RunJoin_ActualRunSources59.alpha1 p with
    | .ok (some a) => a
    | _ => zeroW)

def semantic (p : Phase) (i : Fin 25) : Exact :=
  embed (decode (PV_RunJoin_SemanticScalar50.raw
    (if i.val=0 then p.sem.challenges.lambda
     else if i.val=1 then p.sem.challenges.chi
     else if i.val=2 then p.sem.challenges.theta
     else if i.val<13 then p.sem.challenges.zc.val[i.val-3]?.getD zeroQ
     else if i.val=13 then p.sem.challenges.mu
     else if i.val=14 then p.sem.challenges.eta
     else p.sem.alpha.val[i.val-15]?.getD zeroQ)))

/-- The fallback makes the family total on malformed Phase inputs. Proving
that successful actual builders use the first branch remains producer work. -/
def point (p : Phase) (i : Fin 2) : AspisR0.ChordGeometry.Point Exact :=
  let x := embed (decode (PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_SemanticPoints50.read p.sem.z i.val).x))
  let y := embed (decode (PV_RunJoin_SemanticScalar50.raw (PV_RunJoin_SemanticPoints50.read p.sem.z i.val).y))
  if h : x^2+y^2=1 then ⟨(x,y),h⟩ else ⟨(1,0),by simp⟩

def querySet (p : Phase) : Finset (Fin 262144) :=
  match PV_RunJoin_ActualRunSources59.finish p with
  | .ok (.Ok publication) =>
    (publication.queries.val.filterMap (fun q => if h : q.val<262144 then some ⟨q.val,h⟩ else none)).toFinset
  | _ => ∅

def challenges (p : Phase) : R0Z.HonestView.Challenges Exact where
  sem := semantic p
  circle := point p
  opening := fun i => value (if i.val=0 then preparedField p prover.PreparedOpening.gamma
    else if i.val=1 then preparedField p prover.PreparedOpening.kappa
    else if i.val=2 then preparedField p prover.PreparedOpening.alpha0 else finalScalar p)
  queries := querySet p

def data (p : Phase) : PV_RunJoin_OpeningImages54.Data where
  c := coefficients p
  p := PV_RunJoin_SemanticMaterialInputs50.alpha p.sem
  x0 := PV_RunJoin_SemanticMaterialInputs50.x0 p.sem
  y0 := PV_RunJoin_SemanticMaterialInputs50.y0 p.sem
  x1 := PV_RunJoin_SemanticMaterialInputs50.x1 p.sem
  y1 := PV_RunJoin_SemanticMaterialInputs50.y1 p.sem
  g := preparedField p prover.PreparedOpening.gamma
  k := preparedField p prover.PreparedOpening.kappa
  a := preparedField p prover.PreparedOpening.alpha0
  b := finalScalar p
  ch := challenges p

theorem canonical_coefficients (p : Phase) : PV_RunJoin_OpeningImages54.Coefficients (data p) := by
  intro l hl j hj
  exact ProverCommitNativeOps47.normalize_canonical _

theorem stored_alpha (p : Phase) : (data p).p=PV_RunJoin_SemanticMaterialInputs50.alpha p.sem := rfl

theorem stored_points (p : Phase) :
    (data p).x0=PV_RunJoin_SemanticMaterialInputs50.x0 p.sem ∧
    (data p).y0=PV_RunJoin_SemanticMaterialInputs50.y0 p.sem ∧
    (data p).x1=PV_RunJoin_SemanticMaterialInputs50.x1 p.sem ∧
    (data p).y1=PV_RunJoin_SemanticMaterialInputs50.y1 p.sem := ⟨rfl,rfl,rfl,rfl⟩

#print axioms zeroQ
#print axioms zeroW
#print axioms rawW
#print axioms coefficients
#print axioms preparedField
#print axioms finalScalar
#print axioms semantic
#print axioms point
#print axioms querySet
#print axioms challenges
#print axioms data
#print axioms canonical_coefficients
#print axioms stored_alpha
#print axioms stored_points
end R1Z.PV_RunJoin_ActualData59
