from NLQ_native import native
for i,h,e in [(3,'entry_eleven_model_control',1),(4,'KMX_checks::KMX_ptr_correct',0),(5,'KMX_checks::KMX_ptr_wrong',1),(6,'process_eleven_duplicate',0),(7,'process_eleven_model_control',1),(8,'stage1_eleven_duplicate',0),(9,'stage1_eleven_model_control',1)]:
 r=native(f'NLQ_K{i:03d}','NLQ_native::'+h)
 assert r['exit_status']==e,(h,r['exit_status'])
