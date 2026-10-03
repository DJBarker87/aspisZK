#!/usr/bin/env python3
"""Create a structural (not semantic) row-to-command index for lead's current draft."""
import hashlib,json
from pathlib import Path
ROOT=Path.cwd(); HERE=ROOT/'.r21-scratch/r433-actual-constructor-fragment/inventory'
TABLE=HERE/'constructor86-command-table.json'
MODEL=ROOT/'.r21-scratch/r433-actual-constructor-fragment/R433ConstructorFragment.UNVERIFIED.lean'
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
t=json.loads(TABLE.read_text()); model=MODEL.read_bytes()
commands={
 0:'.live 0',1:'.live 5',2:'.live 2',3:'.metadata 2 1',4:'.live 3',5:'.live 4',6:'.live 8',7:'.rawSlice 8 1 1',8:'.cast 4 8 .sharedFatToNonNullFat',9:'.dead 8',10:'.live 9',11:'.live 10',12:'.cast 10 4 .nonNullFatToMutFat',13:'.cast 9 10 .mutFatToMutThin',14:'.dead 10',15:'.cast 3 9 .mutThinToNonNullThin',16:'.dead 9',17:'.dead 4',19:'.live 11',20:'.marker 11',21:'.iterator 0 3 5 11',22:'.dead 3',23:'.dead 2',24:'.dead 5',25:'.dead 1',26:'.dead 11',27:'.ret'}
rows=[]
for i,s in enumerate(t['statement_commands']):
 if i==18:
  rows.append({'native_statement_index':i,'native_statement_id':s['statement_id'],'native_span':s['span'],'native_opcode':'Switch.If(Global31)',
    'model_command':'globalIf 31','then_arm':[{'native_index':a,'native_statement_id':q['statement_id'],'native_opcode':q['opcode'],'model_command':c} for a,(q,c) in enumerate(zip(s['then_arm']['statements'],['.cast 5 2 .wordToSharedThin']))],
    'else_arm':[{'native_index':a,'native_statement_id':q['statement_id'],'native_opcode':q['opcode'],'model_command':c} for a,(q,c) in enumerate(zip(s['else_arm']['statements'],['.live 6','.live 7','.cast 7 3 .nonNullThinToMutThin','.offset 6 7 2','.dead 7','.cast 5 6 .mutThinToSharedThin','.dead 6']))]})
 else:
  rows.append({'native_statement_index':i,'native_statement_id':s['statement_id'],'native_span':s['span'],'native_opcode':s['opcode'],'native_local':s.get('local',s.get('destination',{}).get('local_alias')),'native_rvalue_opcode':s.get('rvalue',{}).get('opcode'),'model_command':commands[i]})
assert len(rows)==28
assert [r['native_statement_index'] for r in rows]==list(range(28))
( HERE/'model-command-binding.json').write_text(json.dumps({
 'kind':'structural AST-command correspondence table; not an execution/correctness theorem',
 'constructor_input_sha256':t['input_sha256'],'constructor_table_sha256':sha(TABLE),
 'model_source_path':str(MODEL.relative_to(ROOT)),'model_source_sha256':sha(MODEL),
 'model_namespace':'AspisV8R19.R433ConstructorFragment','mapped_model_source_region':'constructor86 definition',
 'top_level_statements':rows,'branch_statement_count':8,
 'structural_result':'Every 28 native top-level statement indices has an explicit model-command position; the sole native Switch.If branch retains 1 then-arm and 7 else-arm statements, each mapped in order.',
 'boundary':'This indexes syntactic opcode/operand/local alignment only. It does not validate the model primitive ABI, pointer lifetime/provenance, allocation assumptions, Rust unsafe preconditions, or source-to-model execution.'
},indent=2,sort_keys=True)+'\n')
print('model source sha256',sha(MODEL),'structural rows',len(rows),'branch rows',8)
