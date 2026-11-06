import NLF_COMBINED_IMPORT
set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
#check NLF_SharedDataLaw.result
#check NLF_ExclusiveDataLaw.result
#check NLF_SharedLamportsLaw.result
#check NLF_ExclusiveLamportsLaw.result
#check NLF_DataLenLaw.result
#check NLF_DataLenLaw.panic_result
#check NLF_LamportsLaw.result
#check NLF_LamportsLaw.panic_result
#check NLF_MetadataLaws.release_payload
#check NLF_MetadataLaws.release_metadata
#check NLF_ViewLaws.map_read
#check NLF_RefCell.no_double_exclusive
#check NLF_RefCell.drop_shared_consumes
#check NLF_CounterLaws.shared_current_counter
#check NLF_CounterLaws.exclusive_zero
#check NLF_SdkBorrowLaw.admitted_events
#check NLF_SdkBorrowLaw.admitted_counter_range
#check NLF_SdkBorrowLaw.unique_live_cell
