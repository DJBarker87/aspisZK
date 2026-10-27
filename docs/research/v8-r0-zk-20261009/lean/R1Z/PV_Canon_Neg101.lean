import R1Z.PV_Canon_Neg
import R1Z.PV_CB_Op101Funs
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_Canon
open Aeneas Aeneas.Std Result
abbrev C101 := PV_CB_ShippedOp101.aspis_core.field.CM31
abbrev Q101 := PV_CB_ShippedOp101.aspis_core.field.QM31
def CanonicalC101 (x : C101) : Prop := M x.a ∧ M x.b
def CanonicalQ101 (x : Q101) : Prop := CanonicalC101 x.c0 ∧ CanonicalC101 x.c1
 theorem neg101_leaf (x : U32) : PV_CB_ShippedOp101.aspis_core.field.M31.neg x =
    ProverRwP7CurrentFieldSource.aspis_core.field.M31.neg x := by
  simp only [PV_CB_ShippedOp101.aspis_core.field.M31.neg,
    PV_CB_ShippedOp101.aspis_core.field.ct.neg,PV_CB_ShippedOp101.aspis_core.field.P,
    ProverRwP7CurrentFieldSource.aspis_core.field.M31.neg,
    ProverRwP7CurrentFieldSource.aspis_core.field.ct.neg,
    ProverRwP7CurrentFieldSource.aspis_core.field.P]
 theorem cneg101 (x : C101) (hx : CanonicalC101 x) :
    ∃ z, PV_CB_ShippedOp101.aspis_core.field.CM31.neg x = .ok z ∧ CanonicalC101 z := by
  obtain ⟨a,ha,hca⟩ := current_neg x.a hx.1
  obtain ⟨b,hb,hcb⟩ := current_neg x.b hx.2
  refine ⟨⟨a,b⟩,?_,hca,hcb⟩
  simp only [PV_CB_ShippedOp101.aspis_core.field.CM31.neg,neg101_leaf,ha,hb,bind_tc_ok]
 theorem qneg101 (x : Q101) (hx : CanonicalQ101 x) :
    ∃ z, PV_CB_ShippedOp101.aspis_core.field.QM31.neg x = .ok z ∧ CanonicalQ101 z := by
  obtain ⟨a,ha,hca⟩ := cneg101 x.c0 hx.1
  obtain ⟨b,hb,hcb⟩ := cneg101 x.c1 hx.2
  refine ⟨⟨a,b⟩,?_,hca,hcb⟩
  simp only [PV_CB_ShippedOp101.aspis_core.field.QM31.neg,ha,hb,bind_tc_ok]
#print axioms neg101_leaf
#print axioms cneg101
#print axioms qneg101
end R1Z.PV_Canon
