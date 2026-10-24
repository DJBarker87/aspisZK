import S1ClosedPrepareProvenanceV1
set_option autoImplicit false
namespace AspisR1CurrentCaller.S1SemanticCarrier
open Aeneas Aeneas.Std Result
open AspisR1CurrentCaller InstalledPreparation AspisR1ClaimPreparedBridge
open OriginalPreparedSource

/-- Copy every field of the returned semantic verifier object. No projection,
canonicalization, fresh transcript or replacement claims owner is used. -/
def currentSem {H : Type} (x : AspisR1PublicPreparation.r1_semantic.Verified H) : r1_semantic.Verified H :=
  {roots:=x.roots,
   challenges:={lambda:=currentQ x.challenges.lambda,chi:=currentQ x.challenges.chi,
     theta:=currentQ x.challenges.theta,zc:=mapArray currentQ x.challenges.zc,
     mu:=currentQ x.challenges.mu,eta:=currentQ x.challenges.eta},
   alpha:=mapArray currentQ x.alpha,claims:=mapArray (mapArray currentQ) x.claims,
   extra:=mapArray currentQ x.extra,before_z1:=mapArray currentQ x.before_z1,
   state_before_z0:=x.state_before_z0,z:=mapArray currentPoint x.z,
   transcript:={state:=x.transcript.state,hash:=x.transcript.hash,next_row:=x.transcript.next_row}}

@[simp] theorem point_old_round (x : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) :
    retainedPoint (currentPoint x)=x := rfl

@[simp] theorem semantic_round {H : Type} (x : AspisR1PublicPreparation.r1_semantic.Verified H) :
    retainedSem (currentSem x)=x := by
  cases x with
  | mk roots challenges alpha claims extra before state z transcript =>
    cases challenges
    cases transcript
    simp only [retainedSem,currentSem,q_round,
      mapArray_inverse currentQ retainedQ q_round,
      mapArray_inverse (mapArray currentQ) (mapArray retainedQ)
        (mapArray_inverse currentQ retainedQ q_round),
      mapArray_inverse currentPoint retainedPoint point_old_round]

@[simp] theorem semantic_back {H : Type} (x : r1_semantic.Verified H) :
    currentSem (retainedSem x)=x := by
  cases x with
  | mk roots challenges alpha claims extra before state z transcript =>
    cases challenges
    cases transcript
    simp only [retainedSem,currentSem,q_round_current,
      mapArray_inverse retainedQ currentQ q_round_current,
      mapArray_inverse (mapArray retainedQ) (mapArray currentQ)
        (mapArray_inverse retainedQ currentQ q_round_current),
      mapArray_inverse retainedPoint currentPoint point_round_current]

def semanticEquiv (H : Type) : AspisR1PublicPreparation.r1_semantic.Verified H ≃ r1_semantic.Verified H :=
  ⟨currentSem,retainedSem,semantic_round,semantic_back⟩

def currentWireError : AspisR1PublicPreparation.r1_wire.Error → r1_wire.Error
  | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow | .Tag r => .Tag r | .Length r => .Length r
  | .NonCanonical r i => .NonCanonical r i | .Boundary i => .Boundary i
  | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes | .Public => .Public

def retainedWireError : r1_wire.Error → AspisR1PublicPreparation.r1_wire.Error
  | .Allocation => .Allocation | .RowOrder a b => .RowOrder a b
  | .InvalidRow => .InvalidRow | .Tag r => .Tag r | .Length r => .Length r
  | .NonCanonical r i => .NonCanonical r i | .Boundary i => .Boundary i
  | .Terminal => .Terminal | .EqualCirclePoints => .EqualCirclePoints
  | .TrailingBytes => .TrailingBytes | .Public => .Public

@[simp] theorem wire_error_round (e : AspisR1PublicPreparation.r1_wire.Error) :
    retainedWireError (currentWireError e)=e := by cases e <;> rfl
@[simp] theorem wire_error_back (e : r1_wire.Error) :
    currentWireError (retainedWireError e)=e := by cases e <;> rfl

#print axioms semantic_round
#print axioms semantic_back
#print axioms semanticEquiv
#print axioms wire_error_round
#print axioms wire_error_back
end AspisR1CurrentCaller.S1SemanticCarrier
