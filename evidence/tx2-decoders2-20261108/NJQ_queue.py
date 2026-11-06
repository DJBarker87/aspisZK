"""Serial owned job queue. Each target gets separate admitted capped scope."""
from pathlib import Path
import subprocess,sys,json
E=Path(__file__).resolve().parent
queues={
 'identity_shape':[['NJQ_shape_run.py','NJQ_K047','inverse'],['NJQ_shape_run.py','NJQ_K056','unimplied'],['NJQ_shape_run.py','NJQ_K060','modifies']],
 'last_model_repairs':[['NJQ_formal.py','NJQ_L061','lean','NJQ_IdentityCut'],['NJQ_formal.py','NJQ_L062','lean','NJQ_Canonical'],['NJQ_formal.py','NJQ_L063','lean','NJQ_ResultCuts']],
 'last_native':[['NJQ_contract.py', 'NJQ_K052', 'registry', 'split_flags', 'invert', 'witness:NJQ_K040'], ['NJQ_contract.py', 'NJQ_K053', 'registry', 'split_zero', 'invert', 'witness:NJQ_K042'], ['NJQ_contract.py', 'NJQ_K054', 'registry', 'split_authority', 'invert', 'witness:NJQ_K044'], ['NJQ_contract.py', 'NJQ_K055', 'entry', 'plain'], ['NJQ_contract.py', 'NJQ_K056', 'entry', 'plain', 'invert'], ['NJQ_contract.py', 'NJQ_K057', 'registry', 'split_bump'], ['NJQ_contract.py', 'NJQ_K058', 'registry', 'split_bump', 'invert', 'witness:NJQ_K057'], ['NJQ_contract.py', 'NJQ_K059', 'entry', 'split_head'], ['NJQ_contract.py', 'NJQ_K060', 'entry', 'split_head', 'invert']],
 'total_carriers':[['NJQ_formal.py','NJQ_L055','lean','NJQ_MasterTotal'],['NJQ_formal.py','NJQ_L056','lean','NJQ_IdentityCut'],['NJQ_formal.py','NJQ_L057','lean','NJQ_Canonical']],
 'final_cuts':[['NJQ_formal.py','NJQ_L052','lean','NJQ_Master'],['NJQ_formal.py','NJQ_L053','lean','NJQ_CheckpointTotal'],['NJQ_formal.py','NJQ_L054','lean','NJQ_MasterCut']],
 'finish_parent_cuts':[['NJQ_formal.py','NJQ_L049','lean','NJQ_Master'],['NJQ_formal.py','NJQ_L050','lean','NJQ_ChildTotal'],['NJQ_formal.py','NJQ_L051','lean','NJQ_CheckpointCut']],
 'repaired_parents':[['NJQ_formal.py','NJQ_L046','lean','NJQ_Checkpoint'],['NJQ_formal.py','NJQ_L047','lean','NJQ_Master'],['NJQ_formal.py','NJQ_L048','lean','NJQ_ChildTotal']],
 'parent_models':[['NJQ_formal.py','NJQ_L042','lean','NJQ_Checkpoint'],['NJQ_formal.py','NJQ_L043','lean','NJQ_Master'],['NJQ_formal.py','NJQ_L044','lean','NJQ_ChildTotal'],['NJQ_formal.py','NJQ_L045','lean','NJQ_Carrier']],
 'focused_next':[['NJQ_formal.py','NJQ_L038','lean','NJQ_MasterBinding'],['NJQ_formal.py','NJQ_L039','lean','NJQ_Checkpoint'],['NJQ_formal.py','NJQ_L040','lean','NJQ_RegistryTotal'],['NJQ_formal.py','NJQ_L041','lean','NJQ_EntryTotal']],
 'registry_split':[['NJQ_contract.py', 'NJQ_K040', 'registry', 'split_flags'], ['NJQ_contract.py', 'NJQ_K041', 'registry', 'split_flags', 'invert'], ['NJQ_contract.py', 'NJQ_K042', 'registry', 'split_zero'], ['NJQ_contract.py', 'NJQ_K043', 'registry', 'split_zero', 'invert'], ['NJQ_contract.py', 'NJQ_K044', 'registry', 'split_authority'], ['NJQ_contract.py', 'NJQ_K045', 'registry', 'split_authority', 'invert'], ['NJQ_contract.py', 'NJQ_K046', 'registry', 'split_delay'], ['NJQ_contract.py', 'NJQ_K047', 'registry', 'split_delay', 'invert'], ['NJQ_contract.py', 'NJQ_K048', 'registry', 'split_head'], ['NJQ_contract.py', 'NJQ_K049', 'registry', 'split_head', 'invert'], ['NJQ_contract.py', 'NJQ_K050', 'registry', 'split_range'], ['NJQ_contract.py', 'NJQ_K051', 'registry', 'split_range', 'invert']], 
 'models':[['NJQ_formal.py','NJQ_L013','lean','NJQ_Library'],['NJQ_formal.py','NJQ_L014','lean','NJQ_IterMut'],['NJQ_formal.py','NJQ_L015','lean','NJQ_Entry']],
 'repaired_models':[['NJQ_formal.py','NJQ_L017','lean','NJQ_IterMut'],['NJQ_formal.py','NJQ_L018','lean','NJQ_Entry']],
 'composition_models':[['NJQ_formal.py','NJQ_L019','lean','NJQ_RegistryCut'],['NJQ_formal.py','NJQ_L020','lean','NJQ_DigestPort'],['NJQ_formal.py','NJQ_L021','lean','NJQ_CheckpointTrace'],['NJQ_formal.py','NJQ_L022','lean','NJQ_MasterTrace']],
 'words_model':[['NJQ_formal.py','NJQ_L023','lean','NJQ_Words']],
 'new_models':[['NJQ_formal.py','NJQ_L023','lean','NJQ_Words'],['NJQ_formal.py','NJQ_L024','lean','NJQ_RegistryCut'],['NJQ_formal.py','NJQ_L025','lean','NJQ_CheckpointTrace'],['NJQ_formal.py','NJQ_L026','lean','NJQ_Reserved']],
 'repair_compositions':[['NJQ_formal.py','NJQ_L027','lean','NJQ_Words'],['NJQ_formal.py','NJQ_L028','lean','NJQ_RegistryCut'],['NJQ_formal.py','NJQ_L029','lean','NJQ_Reserved']],
 'remaining_cuts':[['NJQ_stages_run.py','NJQ_K022','master_step','invert'],['NJQ_prefixes_run.py','NJQ_K023','checkpoint_head'],['NJQ_prefixes_run.py','NJQ_K024','checkpoint_head','invert'],['NJQ_prefixes_run.py','NJQ_K025','master_head'],['NJQ_prefixes_run.py','NJQ_K026','master_head','invert']],
 'body_models':[['NJQ_formal.py','NJQ_L030','lean','NJQ_RegistryCut'],['NJQ_formal.py','NJQ_L031','lean','NJQ_EntryCut'],['NJQ_formal.py','NJQ_L032','lean','NJQ_Header']],
 'constructors':[['NJQ_constructors_run.py','NJQ_K027','child_boundaries'],['NJQ_constructors_run.py','NJQ_K028','child_boundaries','invert'],['NJQ_constructors_run.py','NJQ_K029','checkpoint_constructor_cut'],['NJQ_constructors_run.py','NJQ_K030','checkpoint_constructor_cut','invert'],['NJQ_constructors_run.py','NJQ_K031','master_constructor_cut'],['NJQ_constructors_run.py','NJQ_K032','master_constructor_cut','invert']],
 'digest_and_result':[['NJQ_digest_cut_run.py','NJQ_K033'],['NJQ_digest_cut_run.py','NJQ_K034','invert'],['NJQ_constructors_run.py','NJQ_K035','checkpoint_constructor_cut'],['NJQ_constructors_run.py','NJQ_K036','checkpoint_constructor_cut','invert']],
 'next_models':[['NJQ_formal.py','NJQ_L033','lean','NJQ_EntryCut'],['NJQ_formal.py','NJQ_L034','lean','NJQ_ArrayAll'],['NJQ_formal.py','NJQ_L035','lean','NJQ_MasterBinding']],
 'repair_final_models':[['NJQ_formal.py','NJQ_L036','lean','NJQ_ArrayAll'],['NJQ_formal.py','NJQ_L037','lean','NJQ_MasterBinding']],
 'registry_control':[['NJQ_contract.py','NJQ_K016','registry','validator','invert']],
}
for argv in queues[sys.argv[1]]:
 r=subprocess.run([sys.executable,str(E/argv[0]),*argv[1:]],cwd=E.parents[1])
 with (E/'NJQ_QUEUE.jsonl').open('a') as f:f.write(json.dumps(dict(queue=sys.argv[1],argv=argv,client_exit=r.returncode))+'\n')
