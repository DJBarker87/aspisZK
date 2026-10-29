import NEB_PointCalls
import Port3_PushFrame
set_option autoImplicit false
namespace NEB_PointSuccess
open Aeneas Aeneas.Std Result AspisR1QueryGeometryActual
open AspisR1.Port3_PushFrame (bind_success)

theorem read_bound {T : Type} {n : Usize} (a : Array T n) (i : Usize) (x : T)
    (read : Array.index_usize a i=ok x) : i.val<n.val := by
  by_contra bad
  have length : a.val.length=n.val := a.property
  have absent : a.val[i.val]?=none := List.getElem?_eq_none (by omega)
  simp [Array.index_usize,absent] at read

/-- Successful output canonicality does not require an independent valid-index
hypothesis: the SAME execution's successful reads establish both table domains. -/
theorem canonical (u : Usize) (point : domain.Point field.M31)
    (run : fast_domain.fibre_point NEA_FieldProduct.ops u=ok point) :
    point.x.val<2147483647 ∧ point.y.val<2147483647 := by
  unfold fast_domain.fibre_point at run
  obtain ⟨ix,_,run⟩ := bind_success _ _ _ run
  obtain ⟨iA,_,run⟩ := bind_success _ _ _ run
  obtain ⟨a,readA,run⟩ := bind_success _ _ _ run
  obtain ⟨left,leftRun,run⟩ := bind_success _ _ _ run
  obtain ⟨iB,_,run⟩ := bind_success _ _ _ run
  obtain ⟨b,readB,run⟩ := bind_success _ _ _ run
  obtain ⟨right,rightRun,run⟩ := bind_success _ _ _ run
  obtain ⟨product,mul,finalRun⟩ := bind_success _ _ _ run
  have ca := NEA_TableCanonical.readA iA (read_bound _ _ _ readA) a readA
  have cb := NEA_TableCanonical.readB iB (read_bound _ _ _ readB) b readB
  have la : fast_domain.table_value NEA_FieldProduct.ops a=ok ⟨a.1,a.2⟩ := by cases a; rfl
  have lb : fast_domain.table_value NEA_FieldProduct.ops b=ok ⟨b.1,b.2⟩ := by cases b; rfl
  have sameLeft := Result.ok.inj (leftRun.symm.trans la)
  have sameRight := Result.ok.inj (rightRun.symm.trans lb)
  rw [sameLeft,sameRight] at mul
  obtain ⟨z,productRun,cz,_⟩ := NEA_PointComplete.emitted_interpretation.multiply
    ⟨a.1,a.2⟩ ⟨b.1,b.2⟩ ca cb
  have same : product=z := Result.ok.inj (mul.symm.trans productRun)
  subst product
  have samePoint : point=({x:=z.a,y:=z.b} : domain.Point field.M31) :=
    (Result.ok.inj finalRun).symm
  rw [samePoint]
  exact cz

#print axioms read_bound
#print axioms canonical
end NEB_PointSuccess
