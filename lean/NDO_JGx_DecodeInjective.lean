import NDO_JGv_LimbEquality
import SAG_DotDecode
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_DecodeInjective
open Aeneas Aeneas.Std
abbrev E := SAQ_WideABI.E
abbrev K := SAQ_WideABI.K

theorem scalar (q r : K) (qc : Port3_FlushInstall.Canonical q) (rc : Port3_FlushInstall.Canonical r)
    (same : CheckpointBytes5Output.ofK q=CheckpointBytes5Output.ofK r) : q=r := by
  have functions := RetainedExactLimbCodec.qm31ExactLimbEquiv.injective same
  apply JGv_LimbEquality.source q r qc rc
  intro k
  have residues := congrArg (fun f=>(f k).val) functions
  change (CheckpointBytes5Output.limb q k).val%2147483647=(CheckpointBytes5Output.limb r k).val%2147483647 at residues
  have qc_limb : (CheckpointBytes5Output.limb q k).val<2147483647 := by
    fin_cases k
    · exact qc.1
    · exact qc.2.1
    · exact qc.2.2.1
    · exact qc.2.2.2
  have rc_limb : (CheckpointBytes5Output.limb r k).val<2147483647 := by
    fin_cases k
    · exact rc.1
    · exact rc.2.1
    · exact rc.2.2.1
    · exact rc.2.2.2
  rw [Nat.mod_eq_of_lt qc_limb,Nat.mod_eq_of_lt rc_limb] at residues
  have equal := congrArg (fun n : Nat=>(n : JGv_QueryRows.F)) residues
  fin_cases k <;> exact equal
#print axioms scalar

theorem source (x y : E) (xc : Port4C_QueryArithmetic.CanonE x) (yc : Port4C_QueryArithmetic.CanonE y)
    (same : CheckpointBytes5Output.ofE x=CheckpointBytes5Output.ofE y) : x=y := by
  have re := congrArg QuadraticAlgebra.re same
  have im := congrArg QuadraticAlgebra.im same
  have low := scalar x.c0 y.c0 ⟨xc.1.1,xc.1.2.1,xc.1.2.2.1,xc.1.2.2.2⟩
    ⟨yc.1.1,yc.1.2.1,yc.1.2.2.1,yc.1.2.2.2⟩ re
  have high := scalar x.c1 y.c1 ⟨xc.2.1,xc.2.2.1,xc.2.2.2.1,xc.2.2.2.2⟩
    ⟨yc.2.1,yc.2.2.1,yc.2.2.2.1,yc.2.2.2.2⟩ im
  rcases x with ⟨x0,x1⟩
  rcases y with ⟨y0,y1⟩
  cases low;cases high;rfl
#print axioms source
end AspisR1.JGx_DecodeInjective
end
