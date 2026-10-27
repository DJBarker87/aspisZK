import SAF_C_SAF_FinalTop
set_option autoImplicit false
noncomputable section
namespace AspisR1.SAF_Deployed
/-- Rc3's deployed statement with nineteen finish premise families removed.
The exact outer binders and same source/model witnesses are retained. -/
theorem deployed := @SAF_C_SAF_FinalTop.deployed
#print axioms deployed
end AspisR1.SAF_Deployed
end
