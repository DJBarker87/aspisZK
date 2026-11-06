from NLF_native import native
for i,h,expected in [(52,'shape_unimplied_control',1),(53,'shape_modifies_control',1),(54,'shape_effect_contract',0),(55,'drop_payload_frame',0),(56,'drop_payload_control',1),(57,'alias_guard',0),(58,'alias_guard_control',1),(59,'exclusive_drop_frame',0),(60,'exclusive_drop_control',1)]:
 r=native(f'NLF_K{i:03d}','NLF_sdk::'+h)
 if r['exit_status']!=expected:raise RuntimeError('STOP unexpected native verdict '+h)
