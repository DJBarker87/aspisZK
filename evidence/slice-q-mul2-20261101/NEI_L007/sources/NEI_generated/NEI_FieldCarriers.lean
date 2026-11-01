import NEI_LineFull.Funs
import NEG_FoldAssociation
import JFv_RawExtractedSemanticCallOpsV20
set_option autoImplicit false
noncomputable section
namespace NEI_FieldCarriers
open Aeneas Aeneas.Std Result
open AspisR1PublicPreparation.RawExtractedSemanticCallOpsV20
namespace N
abbrev C := NEI_LineFull.aspis_core.field.CM31
abbrev Q := NEI_LineFull.aspis_core.field.QM31
abbrev E := NEI_LineFull.aspis_core.field.wide_exact.WideExact
end N
namespace C
abbrev C := AspisR1CurrentWide.field.CM31
abbrev Q := AspisR1CurrentWide.field.QM31
abbrev E := AspisR1CurrentWide.field.wide_exact.WideExact
end C

def toC (x : N.C) : C.C := ⟨x.a,x.b⟩
def fromC (x : C.C) : N.C := ⟨x.a,x.b⟩
def toQ (x : N.Q) : C.Q := ⟨toC x.c0,toC x.c1⟩
def fromQ (x : C.Q) : N.Q := ⟨fromC x.c0,fromC x.c1⟩
def toE (x : N.E) : C.E := ⟨toQ x.c0,toQ x.c1⟩
def fromE (x : C.E) : N.E := ⟨fromQ x.c0,fromQ x.c1⟩

theorem fromtoC (x : N.C) : fromC (toC x) = x := by
  cases x
  rfl

theorem tofromC (x : C.C) : toC (fromC x) = x := by
  cases x
  rfl

theorem bindC {B B' : Type} (F : B → B') (r : Result N.C) (k : N.C → Result B) :
    resultMap F (r >>= k) =
      (resultMap toC r) >>= (fun y => resultMap F (k (fromC y))) :=
  resultMap_bind_transport toC fromC fromtoC F r k

theorem fromtoQ (x : N.Q) : fromQ (toQ x) = x := by
  cases x
  rfl

theorem tofromQ (x : C.Q) : toQ (fromQ x) = x := by
  cases x
  rfl

theorem bindQ {B B' : Type} (F : B → B') (r : Result N.Q) (k : N.Q → Result B) :
    resultMap F (r >>= k) =
      (resultMap toQ r) >>= (fun y => resultMap F (k (fromQ y))) :=
  resultMap_bind_transport toQ fromQ fromtoQ F r k

theorem fromtoE (x : N.E) : fromE (toE x) = x := by
  cases x
  rfl

theorem tofromE (x : C.E) : toE (fromE x) = x := by
  cases x
  rfl

theorem bindE {B B' : Type} (F : B → B') (r : Result N.E) (k : N.E → Result B) :
    resultMap F (r >>= k) =
      (resultMap toE r) >>= (fun y => resultMap F (k (fromE y))) :=
  resultMap_bind_transport toE fromE fromtoE F r k

theorem okC (a b : U32) : resultMap toC (ok (⟨a,b⟩ : N.C)) = ok (⟨a,b⟩ : C.C) := rfl

theorem okQ (a b : N.C) : resultMap toQ (ok (⟨a,b⟩ : N.Q)) = ok (⟨toC a,toC b⟩ : C.Q) := rfl

theorem okE (a b : N.Q) : resultMap toE (ok (⟨a,b⟩ : N.E)) = ok (⟨toQ a,toQ b⟩ : C.E) := rfl

theorem m_add (x y : U32) : NEI_LineFull.aspis_core.field.M31.add x y = AspisR1CurrentWide.field.M31.add x y := rfl

theorem m_sub (x y : U32) : NEI_LineFull.aspis_core.field.M31.sub x y = AspisR1CurrentWide.field.M31.sub x y := rfl

theorem m_mul (x y : U32) : NEI_LineFull.aspis_core.field.M31.mul x y = AspisR1CurrentWide.field.M31.mul x y := rfl

theorem m_reduce_u64 (x : U64) : NEI_LineFull.aspis_core.field.M31.reduce_u64 x = AspisR1CurrentWide.field.M31.reduce_u64 x := rfl

theorem m_double (x : U32) : NEI_LineFull.aspis_core.field.M31.double x = AspisR1CurrentWide.field.M31.double x := rfl

theorem bindWord {B B' : Type} (F : B → B') (r : Result U32) (k : U32 → Result B) :
    resultMap F (r >>= k) = r >>= (fun y => resultMap F (k y)) :=
  resultMap_bind F r k
#print axioms bindWord

#print axioms fromtoC
#print axioms tofromC
#print axioms bindC
#print axioms fromtoQ
#print axioms tofromQ
#print axioms bindQ
#print axioms fromtoE
#print axioms tofromE
#print axioms bindE
#print axioms okC
#print axioms okQ
#print axioms okE
#print axioms m_add
#print axioms m_sub
#print axioms m_mul
#print axioms m_reduce_u64
#print axioms m_double
end NEI_FieldCarriers
end
