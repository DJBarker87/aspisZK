import NDO_JGw_GeometryReads
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGw_Inverses
open Aeneas Aeneas.Std Result

def inverse {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 10) : Array U32 5#usize :=
  Classical.choose (JGw_GeometryReads.source err seed i)

theorem read {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 10) :
    Port5Q1_GeometryBinding.forQuery (JGp_Geometry.value err seed) (JGw_GeometryReads.cursor i)=ok (inverse err seed i) :=
  (Classical.choose_spec (JGw_GeometryReads.source err seed i)).1
#print axioms read

theorem decoded {C : Type} (err : C) (seed : Port3_NativeGeometryBody.Ops C) (i : Fin 10) (j : Fin 5) :
    S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane (inverse err seed i) j)=
      (S7JoinBasisMachine.decode ((JGp_Rows.value i).words[j.val]?.getD 0#u32))⁻¹ :=
  (Classical.choose_spec (JGw_GeometryReads.source err seed i)).2.2 j
#print axioms decoded
end AspisR1.JGw_Inverses
end
