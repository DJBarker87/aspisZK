import JFw_TX2_CircleNumbers
set_option autoImplicit false
noncomputable section
namespace AspisR1.JFw_TX2_CircleCoefficients
open Aeneas Aeneas.Std Result
open JFw_TX2_CircleNumbers
def d0 : FE := JFw_TX2_PowersExplicit.decode JFw_TX2_Dot0.value
def d1 : FE := JFw_TX2_PowersExplicit.decode JFw_TX2_Dot1.value
def d2 : FE := JFw_TX2_PowersExplicit.decode JFw_TX2_Dot2.value
def d3 : FE := JFw_TX2_PowersExplicit.decode JFw_TX2_Dot3.value
theorem coefficient0 : (d0+d1+d2+d3)*536870912=h0 := by
  change ((⟨⟨⟨1842200909,1208862427⟩,⟨838681037,572472952⟩⟩,⟨⟨541380581,1864862151⟩,⟨1660777595,1103381136⟩⟩⟩+⟨⟨⟨1594855972,58894088⟩,⟨578797813,626740424⟩⟩,⟨⟨1574036973,1804222405⟩,⟨938683893,984465438⟩⟩⟩+⟨⟨⟨1347065123,438591365⟩,⟨1284475829,1677210292⟩⟩,⟨⟨1472717172,2099714719⟩,⟨1572697310,1548192378⟩⟩⟩+⟨⟨⟨742323479,1312972604⟩,⟨1244769140,478125974⟩⟩,⟨⟨1329886131,605025761⟩,⟨692692841,1013742790⟩⟩⟩)*536870912 : FE)=h0
  unfold h0
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient1 : (d0-d1-d2+d3)*(536870912*1029545577)=h1 := by
  change ((⟨⟨⟨1842200909,1208862427⟩,⟨838681037,572472952⟩⟩,⟨⟨541380581,1864862151⟩,⟨1660777595,1103381136⟩⟩⟩-⟨⟨⟨1594855972,58894088⟩,⟨578797813,626740424⟩⟩,⟨⟨1574036973,1804222405⟩,⟨938683893,984465438⟩⟩⟩-⟨⟨⟨1347065123,438591365⟩,⟨1284475829,1677210292⟩⟩,⟨⟨1472717172,2099714719⟩,⟨1572697310,1548192378⟩⟩⟩+⟨⟨⟨742323479,1312972604⟩,⟨1244769140,478125974⟩⟩,⟨⟨1329886131,605025761⟩,⟨692692841,1013742790⟩⟩⟩)*(536870912*1029545577) : FE)=h1
  unfold h1
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient2 : (d0+d1-d2-d3)*(536870912*243259912)=h2 := by
  change ((⟨⟨⟨1842200909,1208862427⟩,⟨838681037,572472952⟩⟩,⟨⟨541380581,1864862151⟩,⟨1660777595,1103381136⟩⟩⟩+⟨⟨⟨1594855972,58894088⟩,⟨578797813,626740424⟩⟩,⟨⟨1574036973,1804222405⟩,⟨938683893,984465438⟩⟩⟩-⟨⟨⟨1347065123,438591365⟩,⟨1284475829,1677210292⟩⟩,⟨⟨1472717172,2099714719⟩,⟨1572697310,1548192378⟩⟩⟩-⟨⟨⟨742323479,1312972604⟩,⟨1244769140,478125974⟩⟩,⟨⟨1329886131,605025761⟩,⟨692692841,1013742790⟩⟩⟩)*(536870912*243259912) : FE)=h2
  unfold h2
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem coefficient3 : (d0-d1+d2-d3)*(536870912*243259912*1029545577)=h3 := by
  change ((⟨⟨⟨1842200909,1208862427⟩,⟨838681037,572472952⟩⟩,⟨⟨541380581,1864862151⟩,⟨1660777595,1103381136⟩⟩⟩-⟨⟨⟨1594855972,58894088⟩,⟨578797813,626740424⟩⟩,⟨⟨1574036973,1804222405⟩,⟨938683893,984465438⟩⟩⟩+⟨⟨⟨1347065123,438591365⟩,⟨1284475829,1677210292⟩⟩,⟨⟨1472717172,2099714719⟩,⟨1572697310,1548192378⟩⟩⟩-⟨⟨⟨742323479,1312972604⟩,⟨1244769140,478125974⟩⟩,⟨⟨1329886131,605025761⟩,⟨692692841,1013742790⟩⟩⟩)*(536870912*243259912*1029545577) : FE)=h3
  unfold h3
  ext <;> norm_num [AspisWideTower.wideU,AspisV8R15.ExactTowerBase.qm31R,
    AspisV8R15.ExactTowerBase.M31Exact,AspisV8R15.ExactTowerBase.P] <;> decide
theorem formula : FoldRuntimeAlgebra.circleWithInverses
    (CheckpointBytes5Output.ofE JFq_Alpha0.scalar)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 243259912)
    (algebraMap Port5Q1_QueryPorts.FP Port5Q1_QueryPorts.FE 1029545577)
    (Port5Q1_OpeningValues.values JFw_TX2_Dots0.value)=JFw_TX2_CircleNumbers.value := by
  unfold FoldRuntimeAlgebra.circleWithInverses
  change (d0+d1+d2+d3)*(4:FE)⁻¹+alpha*
    ((d0-d1-d2+d3)*((4:FE)⁻¹*1029545577)+alpha*
      ((d0+d1-d2-d3)*((4:FE)⁻¹*243259912)+alpha*
        ((d0-d1+d2-d3)*((4:FE)⁻¹*243259912*1029545577))))=_
  rw [quarter,coefficient0,coefficient1,coefficient2,coefficient3,horner2,horner1,horner0]
#print axioms coefficient0
#print axioms coefficient1
#print axioms coefficient2
#print axioms coefficient3
#print axioms formula
end AspisR1.JFw_TX2_CircleCoefficients
end
