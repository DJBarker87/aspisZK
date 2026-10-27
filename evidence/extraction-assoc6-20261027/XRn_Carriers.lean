import XRk_FieldExternal
import ExtractedPreparedModel
open Aeneas Aeneas.Std Result
set_option autoImplicit false
namespace XRn_Carriers
namespace C
abbrev Q := AspisR1PublicPreparation.aspis_core.field.QM31
abbrev E := AspisR1PublicPreparation.aspis_core.field.WideExact
abbrev V := AspisR1PublicPreparation.transport.Variant
abbrev Point := AspisR1PublicPreparation.aspis_core.circle.SecureCirclePoint
abbrev Challenges := AspisR1PublicPreparation.r1_wire.Challenges
abbrev Sem := AspisR1PublicPreparation.r1_semantic.Verified
abbrev ST := AspisR1PublicPreparation.r1_wire.SemanticTranscript
abbrev T := AspisR1PublicPreparation.transcript.Transcript
abbrev View := AspisR1PublicPreparation.verifier.View
abbrev Prepared := AspisR1PublicPreparation.verifier.Prepared
abbrev D := AspisR1PublicPreparation.aspis_core.Digest32
abbrev Err := AspisR1PublicPreparation.verifier.Error
end C
namespace E
abbrev Q := XRk_Release.aspis_core.field.QM31
abbrev V := XRk_Release.transport.Variant
abbrev Point := XRk_Release.aspis_core.circle.SecureCirclePoint
abbrev Challenges := XRk_Release.aspis_core.state_only_prefix.r0.Challenges
abbrev Sem := XRk_Release.r1_semantic.Verified
abbrev ST := XRk_Release.r1_wire.SemanticTranscript
abbrev T := XRk_Release.transcript.Transcript
abbrev View := XRk_Release.verifier.View
abbrev Prepared := XRk_Release.verifier.Prepared
abbrev D := XRk_Release.aspis_core.digest.Digest32
abbrev Err := XRk_Release.verifier.Error
end E

def arr {A B : Type} {N : Usize} (f : A → B) (a : Array A N) : Array B N :=
  ⟨a.val.map f,by simpa only [List.length_map] using a.property⟩
def cq := XRk_FieldExternal.oldQ
def eq := XRk_FieldExternal.newQ
def cv : E.V → C.V | .S1 => .S1 | .S2 => .S2 | .D => .D
def ev : C.V → E.V | .S1 => .S1 | .S2 => .S2 | .D => .D
def cp (p : E.Point) : C.Point := ⟨cq p.x,cq p.y⟩
def ep (p : C.Point) : E.Point := ⟨eq p.x,eq p.y⟩
def cc (s : E.Challenges) : C.Challenges :=
  ⟨cq s.lambda,cq s.chi,cq s.theta,arr cq s.zc,cq s.mu,cq s.eta⟩
def ec (s : C.Challenges) : E.Challenges :=
  ⟨eq s.lambda,eq s.chi,eq s.theta,arr eq s.zc,eq s.mu,eq s.eta⟩
def cst {H : Type} (s : E.ST H) : C.ST H := ⟨s.state,s.hash,s.next_row⟩
def est {H : Type} (s : C.ST H) : E.ST H := ⟨s.state,s.hash,s.next_row⟩
def ct {H : Type} (s : E.T H) : C.T H := ⟨s.state,s.hash⟩
def et {H : Type} (s : C.T H) : E.T H := ⟨s.state,s.hash⟩
def cs {H : Type} (s : E.Sem H) : C.Sem H :=
  ⟨s.roots,cc s.challenges,arr cq s.alpha,arr (arr cq) s.claims,
    arr cq s.extra,arr cq s.before_z1,s.state_before_z0,arr cp s.z,cst s.transcript⟩
def es {H : Type} (s : C.Sem H) : E.Sem H :=
  ⟨s.roots,ec s.challenges,arr eq s.alpha,arr (arr eq) s.claims,
    arr eq s.extra,arr eq s.before_z1,s.state_before_z0,arr ep s.z,est s.transcript⟩
def cview (v : E.View) : C.View :=
  ⟨cv v.variant,v.semantic,v.y1,v.inactive,v.round0,v.folded_root,v.round1,v.final_message,v.query_bytes⟩
def eview (v : C.View) : E.View :=
  ⟨ev v.variant,v.semantic,v.y1,v.inactive,v.round0,v.folded_root,v.round1,v.final_message,v.query_bytes⟩
def cprepared (p : E.Prepared) : C.Prepared :=
  ⟨cv p.variant,p.roots,p.gamma,p.kappa,p.alpha,cq p.rho,p.queries,
    arr cq p.semantic_alpha,arr cp p.z,p.claim,p.state⟩
def eprepared (p : C.Prepared) : E.Prepared :=
  ⟨ev p.variant,p.roots,p.gamma,p.kappa,p.alpha,eq p.rho,p.queries,
    arr eq p.semantic_alpha,arr ep p.z,p.claim,p.state⟩
def cd {H : Type} (d : E.D H) : C.D H := ⟨d.coremarkerCopyInst,d.digest⟩
def ed {H : Type} (d : C.D H) : E.D H := ⟨d.coremarkerCopyInst,d.digest⟩
def ce : E.Err → C.Err
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation
def ee : C.Err → E.Err
 | .Parse => .Parse | .Semantic => .Semantic | .Transcript => .Transcript
 | .Relation => .Relation | .Merkle => .Merkle | .Query => .Query
 | .Checkpoint => .Checkpoint | .Allocation => .Allocation

def inner {A B F G : Type} (f : A → B) (g : F → G) : core.result.Result A F → core.result.Result B G
 | .Ok a => .Ok (f a) | .Err e => .Err (g e)
def mapR {A B : Type} (f : A → B) (r : Result A) : Result B := do
 let a ← r
 ok (f a)

@[simp] theorem cq_eq (q : C.Q) : cq (eq q)=q := by rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
@[simp] theorem eq_cq (q : E.Q) : eq (cq q)=q := by rcases q with ⟨⟨a,b⟩,⟨c,d⟩⟩; rfl
@[simp] theorem cv_ev (v : C.V) : cv (ev v)=v := by cases v <;> rfl
@[simp] theorem ev_cv (v : E.V) : ev (cv v)=v := by cases v <;> rfl
@[simp] theorem cp_ep (p : C.Point) : cp (ep p)=p := by cases p; simp [cp,ep]
@[simp] theorem ep_cp (p : E.Point) : ep (cp p)=p := by cases p; simp [cp,ep]
@[simp] theorem arr_inverse {A B : Type} {N : Usize} (f : A → B) (g : B → A)
 (h : ∀ x,g (f x)=x) (a : Array A N) : arr g (arr f a)=a := by
 apply Subtype.ext
 simp only [arr,List.map_map]
 have fg : g ∘ f = id := funext h
 rw [fg,List.map_id]
@[simp] theorem cc_ec (s : C.Challenges) : cc (ec s)=s := by cases s; simp [cc,ec]
@[simp] theorem ec_cc (s : E.Challenges) : ec (cc s)=s := by cases s; simp [cc,ec]
@[simp] theorem cst_est {H : Type} (s : C.ST H) : cst (est s)=s := by cases s; rfl
@[simp] theorem est_cst {H : Type} (s : E.ST H) : est (cst s)=s := by cases s; rfl
@[simp] theorem ct_et {H : Type} (s : C.T H) : ct (et s)=s := by cases s; rfl
@[simp] theorem et_ct {H : Type} (s : E.T H) : et (ct s)=s := by cases s; rfl
@[simp] theorem cs_es {H : Type} (s : C.Sem H) : cs (es s)=s := by cases s; simp [cs,es]
@[simp] theorem es_cs {H : Type} (s : E.Sem H) : es (cs s)=s := by cases s; simp [cs,es]
@[simp] theorem cview_eview (v : C.View) : cview (eview v)=v := by cases v; simp [cview,eview]
@[simp] theorem eview_cview (v : E.View) : eview (cview v)=v := by cases v; simp [cview,eview]
@[simp] theorem cprepared_eprepared (p : C.Prepared) : cprepared (eprepared p)=p := by cases p; simp [cprepared,eprepared]
@[simp] theorem eprepared_cprepared (p : E.Prepared) : eprepared (cprepared p)=p := by cases p; simp [cprepared,eprepared]
@[simp] theorem cd_ed {H : Type} (d : C.D H) : cd (ed d)=d := by cases d; rfl
@[simp] theorem ed_cd {H : Type} (d : E.D H) : ed (cd d)=d := by cases d; rfl
@[simp] theorem ce_ee (e : C.Err) : ce (ee e)=e := by cases e <;> rfl
@[simp] theorem ee_ce (e : E.Err) : ee (ce e)=e := by cases e <;> rfl

theorem mapR_bind {A B F : Type} (f : B → F) (r : Result A) (k : A → Result B) :
 mapR f (r >>= k) = r >>= (fun a=>mapR f (k a)) := by cases r <;> rfl

theorem nested_roundtrip (r : Result (core.result.Result E.Prepared E.Err)) :
 mapR (inner eprepared ee) (mapR (inner cprepared ce) r)=r := by
 cases r with
 | ok x => cases x <;> simp [mapR,inner]
 | fail e => rfl
 | div => rfl

#print axioms cq_eq
#print axioms eq_cq
#print axioms cv_ev
#print axioms ev_cv
#print axioms cp_ep
#print axioms ep_cp
#print axioms arr_inverse
#print axioms cc_ec
#print axioms ec_cc
#print axioms cst_est
#print axioms est_cst
#print axioms ct_et
#print axioms et_ct
#print axioms cs_es
#print axioms es_cs
#print axioms cview_eview
#print axioms eview_cview
#print axioms cprepared_eprepared
#print axioms eprepared_cprepared
#print axioms cd_ed
#print axioms ed_cd
#print axioms ce_ee
#print axioms ee_ce
#print axioms mapR_bind
#print axioms nested_roundtrip
end XRn_Carriers
