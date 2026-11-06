from NLF_native import native
for i,h,expected in [(44,'three_copy_window',0),(45,'three_copy_control',1),(46,'seven_cleanup',0),(47,'seven_cleanup_control',1),(48,'shape_weak_contract',0),(49,'shape_inverse_control',1),(50,'shape_real_body',0),(51,'shape_unimplied_control',1),(52,'shape_modifies_control',1),(53,'shape_effect_contract',0),(54,'drop_payload_frame',0),(55,'drop_payload_control',1),(56,'alias_guard',0),(57,'alias_guard_control',1),(58,'lamports_exclusive_control',1),(59,'exclusive_drop_frame',0),(60,'exclusive_wrong_counter',1)]:
 r=native(f'NLF_K{i:03d}','NLF_sdk::'+h)
 if r['exit_status']!=expected:raise RuntimeError('STOP unexpected native verdict '+h)
