from NLF_native import native
for i,h in [(2,'shared_wrong_cell'),(3,'exclusive_free'),(4,'exclusive_wrong_counter'),(5,'KMX_checks::KMX_ptr_correct'),(6,'KMX_checks::KMX_ptr_wrong')]:
 r=native(f'NLF_K{i:03d}','NLF_sdk::'+h)
