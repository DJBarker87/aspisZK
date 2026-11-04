import NGN_RawTypes
import NFW_PreparedPort
set_option autoImplicit false
noncomputable section
namespace AspisR1.NGN_TypeTransport
open Aeneas Aeneas.Std Result

def c (x : NGN_Actual.aspis_core.field.CM31) : AspisR1PublicPreparation.aspis_core.field.CM31 := ⟨x.a,x.b⟩
def rc (x : AspisR1PublicPreparation.aspis_core.field.CM31) : NGN_Actual.aspis_core.field.CM31 := ⟨x.a,x.b⟩
def q (x : NGN_Actual.aspis_core.field.QM31) : AspisR1PublicPreparation.aspis_core.field.QM31 := ⟨c x.c0,c x.c1⟩
def rq (x : AspisR1PublicPreparation.aspis_core.field.QM31) : NGN_Actual.aspis_core.field.QM31 := ⟨rc x.c0,rc x.c1⟩
def e (x : NGN_Actual.aspis_core.field.wide_exact.WideExact) : AspisR1PublicPreparation.aspis_core.field.WideExact := ⟨q x.c0,q x.c1⟩
def re (x : AspisR1PublicPreparation.aspis_core.field.WideExact) : NGN_Actual.aspis_core.field.wide_exact.WideExact := ⟨rq x.c0,rq x.c1⟩
def point (x : NGN_Actual.aspis_core.circle.SecureCirclePoint) : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint := ⟨q x.x,q x.y⟩
def rpoint (x : AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint) : NGN_Actual.aspis_core.circle.SecureCirclePoint := ⟨rq x.x,rq x.y⟩
def variant : NGN_Actual.transport.Variant → AspisR1PublicPreparation.transport.Variant | .S1=>.S1 | .S2=>.S2 | .D=>.D
def rvariant : AspisR1PublicPreparation.transport.Variant → NGN_Actual.transport.Variant | .S1=>.S1 | .S2=>.S2 | .D=>.D

def map {A B : Type} {N : Usize} (f : A→B) (x : Array A N) : Array B N := ⟨x.val.map f,by simpa using x.property⟩
theorem map_inverse {A B : Type} {N : Usize} (f : A→B) (g : B→A)
 (h : ∀ x,g (f x)=x) (x : Array A N) : map g (map f x)=x := by
 apply Subtype.ext
 simp [map,List.map_map,Function.comp_def,h]

theorem q_roundtrip (x : NGN_Actual.aspis_core.field.QM31) : rq (q x)=x := by
 rcases x with ⟨⟨a,b⟩,⟨c,d⟩⟩;rfl
theorem e_roundtrip (x : NGN_Actual.aspis_core.field.wide_exact.WideExact) : re (e x)=x := by
 rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩;rfl
theorem point_roundtrip (x : NGN_Actual.aspis_core.circle.SecureCirclePoint) : rpoint (point x)=x := by
 rcases x with ⟨⟨⟨a,b⟩,⟨c,d⟩⟩,⟨⟨e,f⟩,⟨g,h⟩⟩⟩;rfl
theorem variant_roundtrip (x : NGN_Actual.transport.Variant) : rvariant (variant x)=x := by cases x <;> rfl

def view (x : NGN_Actual.verifier.View) : AspisR1PublicPreparation.verifier.View :=
 {variant:=variant x.variant,semantic:=x.semantic,y1:=x.y1,inactive:=e x.inactive,
  round0:=x.round0,folded_root:=x.folded_root,round1:=x.round1,
  final_message:=x.final_message,query_bytes:=x.query_bytes}
def rview (x : AspisR1PublicPreparation.verifier.View) : NGN_Actual.verifier.View :=
 {variant:=rvariant x.variant,semantic:=x.semantic,y1:=x.y1,inactive:=re x.inactive,
  round0:=x.round0,folded_root:=x.folded_root,round1:=x.round1,
  final_message:=x.final_message,query_bytes:=x.query_bytes}
theorem view_roundtrip (x : NGN_Actual.verifier.View) : rview (view x)=x := by
 cases x
 simp only [view,rview,variant_roundtrip,e_roundtrip]

def transcript {H : Type} (x : NGN_Actual.transcript.Transcript H) : AspisR1PublicPreparation.transcript.Transcript H := ⟨x.state,x.hash⟩
def wireTranscript {H : Type} (x : NGN_Actual.r1_wire.SemanticTranscript H) : AspisR1PublicPreparation.r1_wire.SemanticTranscript H :=
 ⟨x.state,x.hash,x.next_row⟩
def semantic {H : Type} (x : NGN_Actual.r1_semantic.Verified H) : AspisR1PublicPreparation.r1_semantic.Verified H :=
 {roots:=x.roots,challenges:=⟨q x.challenges.lambda,q x.challenges.chi,q x.challenges.theta,
  map q x.challenges.zc,q x.challenges.mu,q x.challenges.eta⟩,
  alpha:=map q x.alpha,claims:=map (map q) x.claims,extra:=map q x.extra,
  before_z1:=map q x.before_z1,state_before_z0:=x.state_before_z0,
  z:=map point x.z,transcript:=wireTranscript x.transcript}

def prepared (x : NGN_Actual.verifier.Prepared) : AspisR1PublicPreparation.verifier.Prepared :=
 {variant:=variant x.variant,roots:=x.roots,gamma:=e x.gamma,kappa:=e x.kappa,
  alpha:=map e x.alpha,rho:=q x.rho,queries:=x.queries,semantic_alpha:=map q x.semantic_alpha,
  z:=map point x.z,claim:=e x.claim,state:=x.state}
def rprepared (x : AspisR1PublicPreparation.verifier.Prepared) : NGN_Actual.verifier.Prepared :=
 {variant:=rvariant x.variant,roots:=x.roots,gamma:=re x.gamma,kappa:=re x.kappa,
  alpha:=map re x.alpha,rho:=rq x.rho,queries:=x.queries,semantic_alpha:=map rq x.semantic_alpha,
  z:=map rpoint x.z,claim:=re x.claim,state:=x.state}

theorem prepared_roundtrip (x : NGN_Actual.verifier.Prepared) : rprepared (prepared x)=x := by
 cases x
 simp only [prepared,rprepared,variant_roundtrip,e_roundtrip,q_roundtrip,
  map_inverse e re e_roundtrip,map_inverse q rq q_roundtrip,map_inverse point rpoint point_roundtrip]

/-- The nominal retarget preserves all eleven returned fields, with explicit
coordinate maps for field/circle carriers and identity for original byte arrays. -/
theorem fields (x : NGN_Actual.verifier.Prepared) :
 (prepared x).variant=variant x.variant ∧ (prepared x).roots=x.roots ∧
 (prepared x).gamma=e x.gamma ∧ (prepared x).kappa=e x.kappa ∧
 (prepared x).alpha=map e x.alpha ∧ (prepared x).rho=q x.rho ∧
 (prepared x).queries=x.queries ∧ (prepared x).semantic_alpha=map q x.semantic_alpha ∧
 (prepared x).z=map point x.z ∧ (prepared x).claim=e x.claim ∧ (prepared x).state=x.state :=
 ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

#print axioms map_inverse
#print axioms q_roundtrip
#print axioms e_roundtrip
#print axioms point_roundtrip
#print axioms variant_roundtrip
#print axioms view_roundtrip
#print axioms prepared_roundtrip
#print axioms fields
end AspisR1.NGN_TypeTransport
