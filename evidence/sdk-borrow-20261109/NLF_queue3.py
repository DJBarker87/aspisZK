from NLF_native import native
for i,h in [(33,'group_conflicts'),(34,'shared_conflict_control'),(35,'group_lamports'),(36,'lamports_shared_control'),(37,'group_scalars'),(38,'data_len_control'),(39,'group_maps'),(40,'shared_map_control'),(41,'exclusive_map_control'),(42,'shared_seven'),(43,'shared_seven_control')]:native(f'NLF_K{i:03d}','NLF_sdk::'+h)
