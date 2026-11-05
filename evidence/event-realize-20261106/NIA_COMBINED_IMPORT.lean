import NGK_COMBINED_IMPORT
import NIA_DriverPackets
import NHZ_CheckpointEvents
import NHZ_Realization
set_option autoImplicit false
noncomputable section
#check @AspisR1.RPx_Deployed.deployed
#check @AspisR1.NHZ_DRIVER.events_from_cuts
#check @AspisR1.NIA_DriverPackets.constructor_cut
#check @AspisR1.NIA_DriverPackets.events_from_constructor
#check @AspisR1.NHZ_EXPERIMENT.same_law
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NIA_DriverPackets.events_from_constructor
#print axioms AspisR1.NHZ_EXPERIMENT.same_law
