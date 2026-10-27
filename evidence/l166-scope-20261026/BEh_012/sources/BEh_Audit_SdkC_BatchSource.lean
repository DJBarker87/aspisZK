import BEf_BatchEffects
import SdkC_BatchSource
/- L166 scoping: inspect actual declarations; no concrete refinement instance asserted. -/
set_option pp.proofs false
#check @AspisR1.SdkC_BatchSource.erasure
#print axioms AspisR1.SdkC_BatchSource.erasure
#check @AspisR1.SdkC_BatchSource.current_source
#print axioms AspisR1.SdkC_BatchSource.current_source
#check @AspisR1.SdkC_BatchSource.stage_source
#print axioms AspisR1.SdkC_BatchSource.stage_source
#check @AspisR1.BEf_BatchEffects.current
#print axioms AspisR1.BEf_BatchEffects.current
#check @AspisR1.BEf_BatchEffects.stage
#print axioms AspisR1.BEf_BatchEffects.stage
#check @AspisR1.BEf_Batches.frames
#print axioms AspisR1.BEf_Batches.frames
