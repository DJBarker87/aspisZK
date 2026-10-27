import R1Z.PV_CB_TowerLaneJoin
import R1Z.PV_CB_Op223CanonicalCallsite
set_option autoImplicit false
namespace R1Z.PV_CB_Op223LaneAgreement
open Aeneas Aeneas.Std Result ProverRwFull PV_CB_Op223CellSupport
variable [ExternalTypes]

/-- Four canonical-domain output gates suffice only with successful result
    witnesses. This is a proof-composition rule, not a discharged native gate. -/
theorem join (f g : Compressor)
    (total : ∀ tag (data : Array U32 16#usize) lambda,
      PV_CB_CanonicalM31.Valid tag → PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid data →
      PV_CB_CanonicalTower.Valid lambda →
      ∃ x y, f tag (Array.to_slice data) lambda = ok x ∧ g tag (Array.to_slice data) lambda = ok y ∧
        x.c0.a = y.c0.a ∧ x.c0.b = y.c0.b ∧ x.c1.a = y.c1.a ∧ x.c1.b = y.c1.b)
    (tag : U32) (data : Array U32 16#usize) (lambda : Q)
    (vt : PV_CB_CanonicalM31.Valid tag) (vd : PV_CB_CanonicalArrays.Valid PV_CB_CanonicalM31.Valid data)
    (vl : PV_CB_CanonicalTower.Valid lambda) :
    f tag (Array.to_slice data) lambda = g tag (Array.to_slice data) lambda := by
  obtain ⟨x,y,hx,hy,h0,h1,h2,h3⟩ := total tag data lambda vt vd vl
  exact PV_CB_TowerLaneJoin.successful _ _ x y hx hy h0 h1 h2 h3
#print axioms join
end R1Z.PV_CB_Op223LaneAgreement
