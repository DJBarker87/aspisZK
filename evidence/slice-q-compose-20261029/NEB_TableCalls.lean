import NEB_PointCalls
import NBG_Constructors
import NEB_PureFrame
import NDH_Geometry
import R17CurrentCM31Semantics
set_option autoImplicit false
namespace NEB_TableCalls
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual

def fromPublic (x : AspisR1PublicPreparation.aspis_core.field.CM31) : field.CM31 := ⟨x.a,x.b⟩

/-- Actual emitted constructor, both full raw words, and the exact table-call
carrier. No canonicality or successful-child premise is introduced. -/
theorem constructor (a b : U32) :
    AspisR1PublicPreparation.aspis_core.field.CM31.new a b=ok ⟨a,b⟩ ∧
    NEA_FieldProduct.ops.new a b=ok ⟨a,b⟩ ∧
    (do let x ← AspisR1PublicPreparation.aspis_core.field.CM31.new a b
        ok (fromPublic x))=NEA_FieldProduct.ops.new a b := by
  exact ⟨NBG_Constructors.cm31_new a b,rfl,by rw [NBG_Constructors.cm31_new];rfl⟩

theorem table_body (a b : U32) :
    fast_domain.table_value NEA_FieldProduct.ops (a,b)=NEA_FieldProduct.ops.new a b ∧
    fast_domain.table_value NEA_FieldProduct.ops (a,b)=ok ⟨a,b⟩ := ⟨rfl,rfl⟩

/-- The selected old table packet's dictionary and the point packet's emitted
field dictionary agree on this ACTUAL constructor call; multiplication unused. -/
theorem selected_table (v : U32 × U32) :
    (do let w ← NDH_Reference.table_ref v;ok (field.CM31.mk w.1 w.2))=
      fast_domain.table_value R17CurrentCM31Semantics.operations v ∧
    fast_domain.table_value R17CurrentCM31Semantics.operations v=
      fast_domain.table_value NEA_FieldProduct.ops v := by
  rcases v with ⟨a,b⟩
  exact ⟨NDH_Geometry.table _ (fun _ _ => rfl) _,rfl⟩

theorem constructor_frame {S Event : Type} (state : S) (a b : U32) :
    AspisR1PublicPreparation.aspis_core.field.CM31.new a b=ok ⟨a,b⟩ ∧
    NEB_PureFrame.run (Event:=Event) state
      (AspisR1PublicPreparation.aspis_core.field.CM31.new a b)=ok (⟨a,b⟩,state,[]) :=
  ⟨NBG_Constructors.cm31_new a b,NEB_PureFrame.successful state _ _ (NBG_Constructors.cm31_new a b)⟩

theorem table_frame {S Event : Type} (state : S) (v : U32 × U32) :
    fast_domain.table_value R17CurrentCM31Semantics.operations v=ok ⟨v.1,v.2⟩ ∧
    fast_domain.table_value NEA_FieldProduct.ops v=ok ⟨v.1,v.2⟩ ∧
    NDH_Reference.table_ref v=ok v ∧
    NEB_PureFrame.run (Event:=Event) state
      (fast_domain.table_value NEA_FieldProduct.ops v)=ok (⟨v.1,v.2⟩,state,[]) := by
  cases v with
  | mk a b => exact ⟨rfl,rfl,rfl,NEB_PureFrame.successful state _ _ rfl⟩

theorem getter_frame {S Event : Type} (state : S) (u : Usize) (admitted : u.val<262144) :
    domain.FibreIndex.get u=ok u ∧ NDH_Reference.fibre_get_ref u=ok u ∧
    NEB_PureFrame.run (Event:=Event) state (domain.FibreIndex.get u)=ok (u,state,[]) :=
  ⟨rfl,rfl,NEB_PureFrame.successful state _ _ rfl⟩

#print axioms constructor
#print axioms table_body
#print axioms selected_table
#print axioms constructor_frame
#print axioms table_frame
#print axioms getter_frame
end NEB_TableCalls
