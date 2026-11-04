import Lean
import NFN_PhaseTransport
import NFS_AccumPart01
import NEI_LineCertificate
import NEI_CircleShared.Funs
import NEI_CircleDomains

-- BEGIN NEI_FieldCM
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_FieldCM
open Aeneas Aeneas.Std Result NFS_NEI_FieldCarriers NFS_NEI_FieldScalar
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem cm_add (x : N.C) (y : N.C) :
    resultMap toC (NEI_LineFull.aspis_core.field.CM31.add x y) =
      AspisR1CurrentWide.field.CM31.add (toC x) (toC y) := by
  simp only [NEI_LineFull.aspis_core.field.CM31.add,
    AspisR1CurrentWide.field.CM31.add, resultMap_bind,
    m_add,m_sub,m_mul,m_reduce_u64,okC,toC]

theorem cm_sub (x : N.C) (y : N.C) :
    resultMap toC (NEI_LineFull.aspis_core.field.CM31.sub x y) =
      AspisR1CurrentWide.field.CM31.sub (toC x) (toC y) := by
  simp only [NEI_LineFull.aspis_core.field.CM31.sub,
    AspisR1CurrentWide.field.CM31.sub, resultMap_bind,
    m_add,m_sub,m_mul,m_reduce_u64,okC,toC]

theorem cm_mul (x : N.C) (y : N.C) :
    resultMap toC (NEI_LineFull.aspis_core.field.CM31.mul x y) =
      AspisR1CurrentWide.field.CM31.mul (toC x) (toC y) := by
  simp only [NEI_LineFull.aspis_core.field.CM31.mul,
    AspisR1CurrentWide.field.CM31.mul, resultMap_bind,
    m_add,m_sub,m_mul,m_reduce_u64,okC,toC]

theorem cm_mul_m31 (x : N.C) (y : U32) :
    resultMap toC (NEI_LineFull.aspis_core.field.CM31.mul_m31 x y) =
      AspisR1CurrentWide.field.CM31.mul_m31 (toC x) y := by
  simp only [NEI_LineFull.aspis_core.field.CM31.mul_m31,
    AspisR1CurrentWide.field.CM31.mul_m31, resultMap_bind,
    m_add,m_sub,m_mul,m_reduce_u64,okC,toC]

theorem by_r (x : N.C) :
    resultMap toC (NEI_LineFull.aspis_core.field.mul_by_r x) =
      AspisR1CurrentWide.field.mul_by_r (toC x) := by
  simp only [NEI_LineFull.aspis_core.field.mul_by_r,
    AspisR1CurrentWide.field.mul_by_r, resultMap_bind,
    m_double,m_add,m_sub,okC,toC]

#print axioms cm_add
#print axioms cm_sub
#print axioms cm_mul
#print axioms cm_mul_m31
#print axioms by_r
end NFS_NEI_FieldCM
end
-- END NEI_FieldCM
-- BEGIN NEI_FieldQM
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_FieldQM
open Aeneas Aeneas.Std Result NFS_NEI_FieldCarriers NFS_NEI_FieldCM
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem qm_add (x : N.Q) (y : N.Q) :
    resultMap toQ (NEI_LineFull.aspis_core.field.QM31.add x y) =
      AspisR1CurrentWide.field.QM31.add (toQ x) (toQ y) := by
  simp only [NEI_LineFull.aspis_core.field.QM31.add,
    AspisR1CurrentWide.field.QM31.add,bindC,cm_add,cm_sub,cm_mul,cm_mul_m31,
    by_r,okQ,toQ,tofromC] <;> rfl

theorem qm_sub (x : N.Q) (y : N.Q) :
    resultMap toQ (NEI_LineFull.aspis_core.field.QM31.sub x y) =
      AspisR1CurrentWide.field.QM31.sub (toQ x) (toQ y) := by
  simp only [NEI_LineFull.aspis_core.field.QM31.sub,
    AspisR1CurrentWide.field.QM31.sub,bindC,cm_add,cm_sub,cm_mul,cm_mul_m31,
    by_r,okQ,toQ,tofromC] <;> rfl

theorem qm_mul (x : N.Q) (y : N.Q) :
    resultMap toQ (NEI_LineFull.aspis_core.field.QM31.mul x y) =
      AspisR1CurrentWide.field.QM31.mul (toQ x) (toQ y) := by
  simp only [NEI_LineFull.aspis_core.field.QM31.mul,
    AspisR1CurrentWide.field.QM31.mul,bindC,cm_add,cm_sub,cm_mul,cm_mul_m31,
    by_r,okQ,toQ,tofromC] <;> rfl

theorem qm_mul_m31 (x : N.Q) (y : U32) :
    resultMap toQ (NEI_LineFull.aspis_core.field.QM31.mul_m31 x y) =
      AspisR1CurrentWide.field.QM31.mul_m31 (toQ x) y := by
  simp only [NEI_LineFull.aspis_core.field.QM31.mul_m31,
    AspisR1CurrentWide.field.QM31.mul_m31,bindC,cm_add,cm_sub,cm_mul,cm_mul_m31,
    by_r,okQ,toQ,tofromC] <;> rfl

theorem mul_u (x : N.Q) :
    resultMap toQ (NEI_LineFull.aspis_core.field.wide_exact.mul_u x) =
      AspisR1CurrentWide.field.wide_exact.mul_u (toQ x) := by
  simp only [NEI_LineFull.aspis_core.field.wide_exact.mul_u,
    AspisR1CurrentWide.field.wide_exact.mul_u,bindC,by_r,okQ,toQ,tofromC] <;> rfl

#print axioms qm_add
#print axioms qm_sub
#print axioms qm_mul
#print axioms qm_mul_m31
#print axioms mul_u
end NFS_NEI_FieldQM
end
-- END NEI_FieldQM
-- BEGIN NEI_FieldWide
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_FieldWide
open Aeneas Aeneas.Std Result NFS_NEI_FieldCarriers NFS_NEI_FieldQM
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20

theorem wide_add (x : N.E) (y : N.E) :
    resultMap toE (NEI_LineFull.aspis_core.field.wide_exact.WideExact.add x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.add (toE x) (toE y) := by
  simp only [NEI_LineFull.aspis_core.field.wide_exact.WideExact.add,
    AspisR1CurrentWide.field.wide_exact.WideExact.add,bindQ,bindWord,
    qm_add,qm_sub,qm_mul,qm_mul_m31,mul_u,okE,toE,tofromQ,
    NEI_LineFull.aspis_core.field.P,AspisR1CurrentWide.field.P] <;> rfl

theorem wide_sub (x : N.E) (y : N.E) :
    resultMap toE (NEI_LineFull.aspis_core.field.wide_exact.WideExact.sub x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.sub (toE x) (toE y) := by
  simp only [NEI_LineFull.aspis_core.field.wide_exact.WideExact.sub,
    AspisR1CurrentWide.field.wide_exact.WideExact.sub,bindQ,bindWord,
    qm_add,qm_sub,qm_mul,qm_mul_m31,mul_u,okE,toE,tofromQ,
    NEI_LineFull.aspis_core.field.P,AspisR1CurrentWide.field.P] <;> rfl

theorem wide_mul (x : N.E) (y : N.E) :
    resultMap toE (NEI_LineFull.aspis_core.field.wide_exact.WideExact.mul x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul (toE x) (toE y) := by
  simp only [NEI_LineFull.aspis_core.field.wide_exact.WideExact.mul,
    AspisR1CurrentWide.field.wide_exact.WideExact.mul,bindQ,bindWord,
    qm_add,qm_sub,qm_mul,qm_mul_m31,mul_u,okE,toE,tofromQ,
    NEI_LineFull.aspis_core.field.P,AspisR1CurrentWide.field.P] <;> rfl

theorem wide_mul_m31 (x : N.E) (y : U32) :
    resultMap toE (NEI_LineFull.aspis_core.field.wide_exact.WideExact.mul_m31 x y) =
      AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31 (toE x) y := by
  simp only [NEI_LineFull.aspis_core.field.wide_exact.WideExact.mul_m31,
    AspisR1CurrentWide.field.wide_exact.WideExact.mul_m31,bindQ,bindWord,
    qm_add,qm_sub,qm_mul,qm_mul_m31,mul_u,okE,toE,tofromQ,
    NEI_LineFull.aspis_core.field.P,AspisR1CurrentWide.field.P] <;> rfl

#print axioms wide_add
#print axioms wide_sub
#print axioms wide_mul
#print axioms wide_mul_m31
end NFS_NEI_FieldWide
end
-- END NEI_FieldWide
-- BEGIN NEI_LineActual
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_LineActual
open Aeneas Aeneas.Std Result NFS_NEI_FieldCarriers NFS_NEI_FieldWide
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1

def rows (a : Array N.E 4#usize) : Array C.E 4#usize :=
  ⟨a.val.map toE, by simpa only [List.length_map] using a.property⟩

theorem body (alpha : N.E) (a : Array N.E 4#usize) (inverse : Array U32 5#usize) :
    resultMap toE (NEI_LineFull.line_fold_with_inverses alpha a inverse) =
      SAQ_LineSource.line (toE alpha) (rows a) inverse := by
  obtain ⟨a,b,c,d,rfl⟩ := SAQ_LineArrays.four a
  obtain ⟨ix,iy,lx,ly,lz,rfl⟩ := SAQ_LineArrays.five inverse
  have mapped : rows (Array.make 4#usize [a,b,c,d]) =
      Array.make 4#usize [toE a,toE b,toE c,toE d] := rfl
  rw [mapped]
  have n0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = ok (a) := rfl
  have n1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = ok (b) := rfl
  have n2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = ok (c) := rfl
  have n3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = ok (d) := rfl
  have c0 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 0#usize = ok (toE a) := rfl
  have c1 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 1#usize = ok (toE b) := rfl
  have c2 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 2#usize = ok (toE c) := rfl
  have c3 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 3#usize = ok (toE d) := rfl
  have i2 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 2#usize = ok lx := rfl
  have i3 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 3#usize = ok ly := rfl
  have i4 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 4#usize = ok lz := rfl
  simp only [NEI_LineFull.line_fold_with_inverses, SAQ_LineSource.line,
    n0,n1,n2,n3,c0,c1,c2,c3,i2,i3,i4,bind_tc_ok]
  simp only [bindE,bindWord,wide_add,wide_sub,wide_mul,wide_mul_m31,
    NFS_NEI_FieldScalar.m_mul,tofromE,NEI_LineFull.QUARTER,SAQ_LineSource.quarter] <;> rfl

#print axioms body
end NFS_NEI_LineActual
end
-- END NEI_LineActual
-- BEGIN NEI_CircleActual
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_CircleActual
open Aeneas Aeneas.Std Result NFS_NEI_FieldCarriers NFS_NEI_FieldWide NFS_NEI_LineActual
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1

theorem body (alpha : N.E) (a : Array N.E 4#usize) (inverse : Array U32 5#usize) :
    resultMap toE (NEI_CircleShared.circle_fold_with_inverses alpha a inverse) =
      FIp_CircleSource.circle (toE alpha) (rows a) inverse := by
  obtain ⟨a,b,c,d,rfl⟩ := SAQ_LineArrays.four a
  obtain ⟨ix,iy,lx,ly,lz,rfl⟩ := SAQ_LineArrays.five inverse
  have mapped : rows (Array.make 4#usize [a,b,c,d]) =
      Array.make 4#usize [toE a,toE b,toE c,toE d] := rfl
  rw [mapped]
  have n0 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 0#usize = ok (a) := rfl
  have n1 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 1#usize = ok (b) := rfl
  have n2 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 2#usize = ok (c) := rfl
  have n3 : Array.index_usize (Array.make 4#usize [a,b,c,d]) 3#usize = ok (d) := rfl
  have c0 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 0#usize = ok (toE a) := rfl
  have c1 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 1#usize = ok (toE b) := rfl
  have c2 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 2#usize = ok (toE c) := rfl
  have c3 : Array.index_usize (Array.make 4#usize [toE a,toE b,toE c,toE d]) 3#usize = ok (toE d) := rfl
  have i0 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 0#usize = ok ix := rfl
  have i1 : Array.index_usize (Array.make 5#usize [ix,iy,lx,ly,lz]) 1#usize = ok iy := rfl
  simp only [NEI_CircleShared.circle_fold_with_inverses, FIp_CircleSource.circle,
    n0,n1,n2,n3,c0,c1,c2,c3,i0,i1,bind_tc_ok]
  simp only [bindE,bindWord,wide_add,wide_sub,wide_mul,wide_mul_m31,
    NFS_NEI_FieldScalar.m_mul,tofromE,NEI_CircleShared.QUARTER,SAQ_LineSource.quarter] <;> rfl

#print axioms body
end NFS_NEI_CircleActual
end
-- END NEI_CircleActual
-- BEGIN NEI_CircleBridge
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_CircleBridge
open Aeneas Aeneas.Std Result NFS_NEI_FieldCarriers NFS_NEI_LineActual NFS_NEI_CircleActual
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1 AspisR1CurrentWide.Proof

/-- The actual extracted source uses identical fields; inverse is unrestricted. -/
def Domain (alpha : N.E) (a : Array N.E 4#usize) : Prop :=
  NEI_CircleDomains.Domain (toE alpha) (rows a)

theorem returns (alpha : N.E) (a : Array N.E 4#usize) (inverse : Array U32 5#usize)
    (domain : Domain alpha a) :
    ∃ out, NEI_CircleShared.circle_fold_with_inverses alpha a inverse = ok out ∧
      NEG_FoldsTypes.circle_fold_with_inverses (toE alpha) (rows a) inverse = ok (toE out) ∧
      CanonicalWide (toE out) := by
  obtain ⟨value,source,canonical⟩ := NEI_CircleDomains.total (toE alpha) (rows a) inverse domain
  have cohort : NEG_FoldsTypes.circle_fold_with_inverses (toE alpha) (rows a) inverse = ok value :=
    (NEG_FoldAssociation.circle _ _ _).trans source
  have mapped := (NFS_NEI_CircleActual.body alpha a inverse).trans source
  cases native : NEI_CircleShared.circle_fold_with_inverses alpha a inverse with
  | fail e => simp only [native,resultMap] at mapped; cases mapped
  | div => simp only [native,resultMap] at mapped; cases mapped
  | ok out =>
    have same : toE out = value := by
      simp only [native,resultMap] at mapped
      exact Result.ok.inj mapped
    exact ⟨out,rfl,by simpa only [same] using cohort,by simpa only [same] using canonical⟩

/-- Full Result and the pure frame are from this same extracted execution. -/
theorem complete {S Event : Type} (state : S) (alpha : N.E)
    (a : Array N.E 4#usize) (inverse : Array U32 5#usize) (domain : Domain alpha a) :
    ∃ out, NEI_CircleShared.circle_fold_with_inverses alpha a inverse = ok out ∧
      CanonicalWide (toE out) ∧
      NEB_PureFrame.run (Event:=Event) state
        (NEI_CircleShared.circle_fold_with_inverses alpha a inverse) = ok (out,state,[]) ∧
      NEG_FoldsTypes.circle_fold_with_inverses (toE alpha) (rows a) inverse = ok (toE out) := by
  obtain ⟨out,native,cohort,canonical⟩ := returns alpha a inverse domain
  exact ⟨out,native,canonical,NEB_PureFrame.successful state _ _ native,cohort⟩

#print axioms returns
#print axioms complete
end NFS_NEI_CircleBridge
end
-- END NEI_CircleBridge
-- BEGIN NEI_LineBridge
set_option autoImplicit false
noncomputable section
namespace NFS_NEI_LineBridge
open Aeneas Aeneas.Std Result NFS_NEI_FieldCarriers NFS_NEI_LineActual
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
open AspisR1 AspisR1CurrentWide.Proof

/-- The actual extracted source uses identical fields; inverse is unrestricted. -/
def Domain (alpha : N.E) (a : Array N.E 4#usize) : Prop :=
  NEI_LineDomains.Domain (toE alpha) (rows a)

theorem returns (alpha : N.E) (a : Array N.E 4#usize) (inverse : Array U32 5#usize)
    (domain : Domain alpha a) :
    ∃ out, NEI_LineFull.line_fold_with_inverses alpha a inverse = ok out ∧
      NEG_FoldsTypes.line_fold_with_inverses (toE alpha) (rows a) inverse = ok (toE out) ∧
      CanonicalWide (toE out) := by
  obtain ⟨value,cohort,canonical⟩ := NEI_LineDomains.total (toE alpha) (rows a) inverse domain
  have source : SAQ_LineSource.line (toE alpha) (rows a) inverse = ok value :=
    (NEG_FoldAssociation.line _ _ _).symm.trans cohort
  have mapped := (NFS_NEI_LineActual.body alpha a inverse).trans source
  cases native : NEI_LineFull.line_fold_with_inverses alpha a inverse with
  | fail e => simp only [native,resultMap] at mapped; cases mapped
  | div => simp only [native,resultMap] at mapped; cases mapped
  | ok out =>
    have same : toE out = value := by
      simp only [native,resultMap] at mapped
      exact Result.ok.inj mapped
    exact ⟨out,rfl,by simpa only [same] using cohort,by simpa only [same] using canonical⟩

/-- Full Result and the pure frame are from this same extracted execution. -/
theorem complete {S Event : Type} (state : S) (alpha : N.E)
    (a : Array N.E 4#usize) (inverse : Array U32 5#usize) (domain : Domain alpha a) :
    ∃ out, NEI_LineFull.line_fold_with_inverses alpha a inverse = ok out ∧
      CanonicalWide (toE out) ∧
      NEB_PureFrame.run (Event:=Event) state
        (NEI_LineFull.line_fold_with_inverses alpha a inverse) = ok (out,state,[]) ∧
      NEG_FoldsTypes.line_fold_with_inverses (toE alpha) (rows a) inverse = ok (toE out) := by
  obtain ⟨out,native,cohort,canonical⟩ := returns alpha a inverse domain
  exact ⟨out,native,canonical,NEB_PureFrame.successful state _ _ native,cohort⟩

#print axioms returns
#print axioms complete
end NFS_NEI_LineBridge
end
-- END NEI_LineBridge

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
