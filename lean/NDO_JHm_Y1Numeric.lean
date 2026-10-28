import NDO_JHm_Y1_00
import NDO_JHm_Y1_10
import NDO_JHm_Y1_20
import NDO_JHm_RowFacts
set_option autoImplicit false
noncomputable section
namespace AspisR1.JHm_Y1Numeric
open Aeneas Aeneas.Std Result AspisR1CurrentPreparedClaim
theorem source (j : Usize) (hj : j.val<29) (out : Concrete.E)
    (call : ClaimParser.field JGe_Payload27.value j=ok out) :
    AspisR1S5ClaimScalarEmbeddedProductSum.scalarEmbed out.c0=
    (JHm_Arithmetic.row 5)[j.val]'(by rw [(show (JHm_Arithmetic.row 5).length=29 from rfl)];exact hj) := by
  interval_cases hv : j.val
  · have same : j=0#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_00.source00)
    rw [eq]
    exact JHm_Y1_00.numeric00
  · have same : j=1#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_00.source01)
    rw [eq]
    exact JHm_Y1_00.numeric01
  · have same : j=2#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_00.source02)
    rw [eq]
    exact JHm_Y1_00.numeric02
  · have same : j=3#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_00.source03)
    rw [eq]
    exact JHm_Y1_00.numeric03
  · have same : j=4#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_00.source04)
    rw [eq]
    exact JHm_Y1_00.numeric04
  · have same : j=5#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_00.source05)
    rw [eq]
    exact JHm_Y1_00.numeric05
  · have same : j=6#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_00.source06)
    rw [eq]
    exact JHm_Y1_00.numeric06
  · have same : j=7#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_00.source07)
    rw [eq]
    exact JHm_Y1_00.numeric07
  · have same : j=8#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_00.source08)
    rw [eq]
    exact JHm_Y1_00.numeric08
  · have same : j=9#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_00.source09)
    rw [eq]
    exact JHm_Y1_00.numeric09
  · have same : j=10#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_10.source10)
    rw [eq]
    exact JHm_Y1_10.numeric10
  · have same : j=11#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_10.source11)
    rw [eq]
    exact JHm_Y1_10.numeric11
  · have same : j=12#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_10.source12)
    rw [eq]
    exact JHm_Y1_10.numeric12
  · have same : j=13#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_10.source13)
    rw [eq]
    exact JHm_Y1_10.numeric13
  · have same : j=14#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_10.source14)
    rw [eq]
    exact JHm_Y1_10.numeric14
  · have same : j=15#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_10.source15)
    rw [eq]
    exact JHm_Y1_10.numeric15
  · have same : j=16#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_10.source16)
    rw [eq]
    exact JHm_Y1_10.numeric16
  · have same : j=17#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_10.source17)
    rw [eq]
    exact JHm_Y1_10.numeric17
  · have same : j=18#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_10.source18)
    rw [eq]
    exact JHm_Y1_10.numeric18
  · have same : j=19#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_10.source19)
    rw [eq]
    exact JHm_Y1_10.numeric19
  · have same : j=20#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_20.source20)
    rw [eq]
    exact JHm_Y1_20.numeric20
  · have same : j=21#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_20.source21)
    rw [eq]
    exact JHm_Y1_20.numeric21
  · have same : j=22#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_20.source22)
    rw [eq]
    exact JHm_Y1_20.numeric22
  · have same : j=23#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_20.source23)
    rw [eq]
    exact JHm_Y1_20.numeric23
  · have same : j=24#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_20.source24)
    rw [eq]
    exact JHm_Y1_20.numeric24
  · have same : j=25#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_20.source25)
    rw [eq]
    exact JHm_Y1_20.numeric25
  · have same : j=26#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_20.source26)
    rw [eq]
    exact JHm_Y1_20.numeric26
  · have same : j=27#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_20.source27)
    rw [eq]
    exact JHm_Y1_20.numeric27
  · have same : j=28#usize := UScalar.eq_of_val_eq hv
    subst j
    have eq := Result.ok.inj (call.symm.trans JHm_Y1_20.source28)
    rw [eq]
    exact JHm_Y1_20.numeric28
#print axioms source
end AspisR1.JHm_Y1Numeric
end
