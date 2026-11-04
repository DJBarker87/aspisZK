import NFS_Folds
import NFP_DotDomains
import FIp_CircleQuery
set_option autoImplicit false
noncomputable section
namespace AspisR1.NFS_FoldInstall
open Aeneas Aeneas.Std Result AspisR1Stage2 NFP_QueryCuts
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
abbrev Native := NFS_NEI_FieldCarriers.N.E

def raw (e : E) : Native := NFS_NEI_FieldCarriers.fromE (SAQ_WideABI.toW e)
def values (v : Dots) : Array Native 4#usize :=
 ⟨v.val.map raw,by simpa only [List.length_map] using v.property⟩
def result (r : Result Native) : Result E :=
 resultMap (fun x=>SAQ_WideABI.fromW (NFS_NEI_FieldCarriers.toE x)) r

theorem rows (v : Dots) : NFS_NEI_LineActual.rows (values v)=SAQ_LineQuery.toValues v := by
 apply Subtype.ext
 simp only [NFS_NEI_LineActual.rows,values,List.map_map,raw,Function.comp_def,
  NFS_NEI_FieldCarriers.tofromE,SAQ_LineQuery.toValues]

theorem map_map {A B C : Type} (f : A → B) (g : B → C) (r : Result A) :
 resultMap g (resultMap f r)=resultMap (fun x=>g (f x)) r := by cases r <;> rfl

theorem line (alpha : E) (v : Dots) (inverse : Array U32 5#usize) :
 result (NEI_LineFull.line_fold_with_inverses (raw alpha) (values v) inverse)=
 SAQ_LineQuery.line alpha v inverse := by
 unfold result
 rw [←map_map NFS_NEI_FieldCarriers.toE SAQ_WideABI.fromW,
  NFS_NEI_LineActual.body,raw,NFS_NEI_FieldCarriers.tofromE,rows]
 unfold SAQ_LineQuery.line
 cases SAQ_LineSource.line (SAQ_WideABI.toW alpha) (SAQ_LineQuery.toValues v) inverse <;> rfl

theorem circle (alpha : E) (v : Dots) (inverse : Array U32 5#usize) :
 result (NEI_CircleShared.circle_fold_with_inverses (raw alpha) (values v) inverse)=
 FIp_CircleQuery.circle alpha v inverse := by
 unfold result
 rw [←map_map NFS_NEI_FieldCarriers.toE SAQ_WideABI.fromW,
  NFS_NEI_CircleActual.body,raw,NFS_NEI_FieldCarriers.tofromE,rows]
 change resultMap SAQ_WideABI.fromW
  (FIp_CircleSource.circle (SAQ_WideABI.toW alpha) (FIp_CircleQuery.toValues v) inverse)=_
 unfold FIp_CircleQuery.circle
 cases FIp_CircleSource.circle (SAQ_WideABI.toW alpha) (FIp_CircleQuery.toValues v) inverse <;> rfl

/-- Both fold PacketDomains are derived from the SAME actual receiver values.
Inverse is unrestricted by these CLOSED callee packets. -/
theorem domains (alpha : E) (v : Dots)
 (ha : Port4C_QueryArithmetic.CanonE alpha)
 (hv : ∀ x∈v.val,Port4C_QueryArithmetic.CanonE x) :
 NFS_NEI_LineBridge.Domain (raw alpha) (values v) ∧
 NFS_NEI_CircleBridge.Domain (raw alpha) (values v) := by
 have a := (SAQ_WideABI.w_canonical alpha).mp ha
 have vs : ∀ x∈(SAQ_LineQuery.toValues v).val,AspisR1CurrentWide.Proof.CanonicalWide x := by
  intro x member
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp member
  exact (SAQ_WideABI.w_canonical y).mp (hv y hy)
 have d : NEI_LineDomains.Domain (SAQ_WideABI.toW alpha) (SAQ_LineQuery.toValues v) := ⟨a,vs⟩
 constructor <;> simpa only [NFS_NEI_LineBridge.Domain,NFS_NEI_CircleBridge.Domain,
  raw,NFS_NEI_FieldCarriers.tofromE,rows] using d
#print axioms rows
#print axioms map_map
#print axioms line
#print axioms circle
#print axioms domains
end AspisR1.NFS_FoldInstall
end
