import NIX_ObservedBody
import NIX_CertificateFrames
set_option autoImplicit false
namespace AspisR1.NJG_Carriers
open Aeneas Aeneas.Std Result
abbrev E := NIX_EmittedTypes.aspis_core.field.QM31
abbrev M := AspisR1PublicPreparation.aspis_core.field.QM31

def mapA {A B : Type} {n : Usize} (f : A→B) (a : Array A n) : Array B n :=
 ⟨a.val.map f,by simp only [List.length_map,a.property]⟩

theorem map_inverse {A B : Type} {n : Usize} (f : A→B) (g : B→A)
 (law : ∀ x,g (f x)=x) (a : Array A n) : mapA g (mapA f a)=a := by
 apply Subtype.ext
 simp [mapA,List.map_map,Function.comp_def,law]

def upQ (q : E) : M := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩
def downQ (q : M) : E := ⟨⟨q.c0.a,q.c0.b⟩,⟨q.c1.a,q.c1.b⟩⟩

theorem q_roundtrip (q : E) : downQ (upQ q)=q := by cases q with | mk c d=>cases c;cases d;rfl
theorem q_back (q : M) : upQ (downQ q)=q := by cases q with | mk c d=>cases c;cases d;rfl

def upPoint (p : NIX_EmittedTypes.aspis_core.circle.SecureCirclePoint) :
 AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint := ⟨upQ p.x,upQ p.y⟩
def downPoint (p : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) :
 NIX_EmittedTypes.aspis_core.circle.SecureCirclePoint := ⟨downQ p.x,downQ p.y⟩

theorem point_roundtrip (p : NIX_EmittedTypes.aspis_core.circle.SecureCirclePoint) :
 downPoint (upPoint p)=p := by cases p;simp only [upPoint,downPoint,q_roundtrip]

def upChallenge (c : NIX_EmittedTypes.aspis_core.state_only_prefix.r0.Challenges) :
 AspisR1PublicPreparation.r1_wire.Challenges :=
 ⟨upQ c.lambda,upQ c.chi,upQ c.theta,mapA upQ c.zc,upQ c.mu,upQ c.eta⟩
def downChallenge (c : AspisR1PublicPreparation.r1_wire.Challenges) :
 NIX_EmittedTypes.aspis_core.state_only_prefix.r0.Challenges :=
 ⟨downQ c.lambda,downQ c.chi,downQ c.theta,mapA downQ c.zc,downQ c.mu,downQ c.eta⟩

theorem challenge_roundtrip (c : NIX_EmittedTypes.aspis_core.state_only_prefix.r0.Challenges) :
 downChallenge (upChallenge c)=c := by
 cases c
 simp only [upChallenge,downChallenge,q_roundtrip,map_inverse upQ downQ q_roundtrip]

def upTranscript {H : Type} (t : NIX_EmittedTypes.r1_wire.SemanticTranscript H) :
 AspisR1PublicPreparation.r1_wire.SemanticTranscript H := ⟨t.state,t.hash,t.next_row⟩
def downTranscript {H : Type} (t : AspisR1PublicPreparation.r1_wire.SemanticTranscript H) :
 NIX_EmittedTypes.r1_wire.SemanticTranscript H := ⟨t.state,t.hash,t.next_row⟩

theorem transcript_roundtrip {H : Type} (t : NIX_EmittedTypes.r1_wire.SemanticTranscript H) :
 downTranscript (upTranscript t)=t := by cases t;rfl

def upVerified {H : Type} (v : NIX_EmittedTypes.r1_semantic.Verified H) :
 AspisR1PublicPreparation.r1_semantic.Verified H :=
 ⟨v.roots,upChallenge v.challenges,mapA upQ v.alpha,mapA (mapA upQ) v.claims,
 mapA upQ v.extra,mapA upQ v.before_z1,v.state_before_z0,mapA upPoint v.z,upTranscript v.transcript⟩
def downVerified {H : Type} (v : AspisR1PublicPreparation.r1_semantic.Verified H) :
 NIX_EmittedTypes.r1_semantic.Verified H :=
 ⟨v.roots,downChallenge v.challenges,mapA downQ v.alpha,mapA (mapA downQ) v.claims,
 mapA downQ v.extra,mapA downQ v.before_z1,v.state_before_z0,mapA downPoint v.z,downTranscript v.transcript⟩

/-- Exact complete carrier, every field, including hash and next_row. No
canonicality or successful endpoint premise; no native/source equation claimed. -/
theorem verified_roundtrip {H : Type} (v : NIX_EmittedTypes.r1_semantic.Verified H) :
 downVerified (upVerified v)=v := by
 cases v
 simp only [upVerified,downVerified,challenge_roundtrip,transcript_roundtrip,
  map_inverse upQ downQ q_roundtrip,map_inverse upPoint downPoint point_roundtrip,
  map_inverse (mapA upQ) (mapA downQ) (map_inverse upQ downQ q_roundtrip)]

theorem verified_injective {H : Type} (a b : NIX_EmittedTypes.r1_semantic.Verified H)
 (same : upVerified a=upVerified b) : a=b := by
 have h:=congrArg downVerified same
 simpa only [verified_roundtrip] using h

#print axioms map_inverse
#print axioms q_roundtrip
#print axioms q_back
#print axioms point_roundtrip
#print axioms challenge_roundtrip
#print axioms transcript_roundtrip
#print axioms verified_roundtrip
#print axioms verified_injective
end AspisR1.NJG_Carriers
