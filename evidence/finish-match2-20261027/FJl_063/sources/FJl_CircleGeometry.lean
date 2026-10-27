import Port5Q1_GeometryAccessor
import Port5Q1_QueryPorts
set_option autoImplicit false
noncomputable section
namespace AspisR1.FJl_CircleGeometry
open Aeneas Aeneas.Std Result AspisR1Stage2
open Port5Q1_QueryPorts
/-- The first two inverse coordinates used by the SAME native circle fold. -/
theorem value (p : verifier.Prepared) (data : MatchingSupport.Data FE)
    (q : Fin 22 → Fin 262144) (rho : FK) (prepare : SessionAPrepare p data q rho)
    (start stop : Usize) (geometry : verifier.QueryGeometry)
    (binding : Port5Q1_GeometryBinding.Binding p.queries start stop geometry)
    (i : Usize) (lo : start.val≤i.val) (hi : i.val<stop.val)
    (inverse : Array U32 5#usize) (z : aspis_core.field.M31)
    (read : Port5Q1_GeometryBinding.forQuery geometry i=ok inverse)
    (zread : alloc.vec.Vec.index (core.slice.index.SliceIndexUsizeSlice aspis_core.field.M31)
      geometry.line_z (Usize.wrapping_sub i geometry.start)=ok z) :
    let j : Fin 22 := ⟨i.val,Nat.lt_of_lt_of_le hi binding.bound⟩
    (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 0)=
      ((Port5Q1_Domain.words (q j).val)[0]?.getD 0)⁻¹) ∧
    (S7JoinBasisMachine.decode (Port5Q1_GeometryBinding.lane inverse 1)=
      ((Port5Q1_Domain.words (q j).val)[1]?.getD 0)⁻¹) := by
  have h := Port5Q1_GeometryAccessor.reads p.queries start stop geometry binding i lo hi inverse z read zread
  have raw := prepare.queries i.val (Nat.lt_of_lt_of_le hi binding.bound)
  exact ⟨by simpa only [raw] using h.2 (0 : Fin 5),by simpa only [raw] using h.2 (1 : Fin 5)⟩
#print axioms value
end AspisR1.FJl_CircleGeometry
end
