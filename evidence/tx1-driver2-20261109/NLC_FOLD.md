# NLC fold-first work

State and event type were defined first in NLC_FinishState. NLC_FinishStep dispatches source-ordered operations on that state, with explicit missing-slot failure; returned Err terminates, outer fail/div are retained by Code. NLC_FinishFold.fold_from_steps proves the chronological append/no-suffix fold on the SAME successive states.

This is a local version of NHZ_DRIVER.events_from_cuts because this stage uses PreparedHashCode (hash state is carried in its digest syntax), while NHZ uses normalized SdkC_Source.Code. AuS1_Trace.run_bind, from the coherent RPz7-retargeted module, supplies the same append algebra. No inverse native log association, sorting, deduplication or runtime digest-value claim is added.

Status: conditional SOURCE fold only. Native step production, all source initialization/argument domains and equality with the actual deployed finish syntax remain OPEN. No parameterized native fold or row root is claimed.
