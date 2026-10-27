"""Field-level wire audits. Source layout offsets are explicit, not inferred from images."""
from pathlib import Path
import runpy,sys,json,hashlib
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent;check='--check' in sys.argv
sys.argv=['JHg_generate.py','--check'];g=runpy.run_path(str(P/'JHg_generate.py'))
layouts={
'Master':[('magic',0,4),('version',4,5),('lanes',5,6),('encoding',6,7),('bump',7,8),('format',8,40),('next_checkpoint',40,48),('lane_mask',48,49),('has_checkpoint',49,50),('reserved0',50,64),('identity_magic',64,68),('identity_version',68,69),('identity_reserved',69,72),('pool',72,104),('mint',104,136),('token',136,168),('asset',168,172),('identity_reserved1',172,176),('domain',176,208),('policy_magic',208,212),('policy_version',212,213),('policy_flags',213,214),('policy_reserved',214,216),('registry_program',216,248),('registry_authority',248,280),('policy_binding',280,312),('reserved1',312,320)]+[(f'last_sequence_{i}',320+8*i,328+8*i) for i in range(8)],
'Forest':[('magic',0,4),('version',4,5),('lanes',5,6),('encoding',6,7),('bump',7,8),('master',8,40),('domain',40,72),('sequence',72,80),('root',80,112)]+[(f'lane_sequence_{i}',112+8*i,120+8*i) for i in range(8)]+[('reserved',176,192)],
'Lane':[('magic',0,4),('version',4,5),('lane',5,6),('lanes',6,7),('depth',7,8),('format',8,40),('master',40,72),('bump',72,73),('reserved',73,80),('tree_magic',80,84),('tree_version',84,85),('tree_depth',85,86),('tree_hash_version',86,87),('tree_encoding',87,88),('next_index',88,96),('root',96,128)]+[(f'frontier_{i}',128+32*i,160+32*i) for i in range(20)],
'Registry':[('magic',0,4),('version',4,5),('flags',5,6),('mode',6,7),('bump',7,8),('pool',8,40),('authority',40,72),('policy',72,104),('generation',104,112),('delay',112,120),('program',120,152),('loader',152,184),('programdata',184,216),('executable_hash',216,248),('programdata_bump',248,249),('reserved',249,256)],
'Entry':[('magic',0,4),('version',4,5),('status',5,6),('statement_version',6,7),('mode',7,8),('pool',8,40),('verifier',40,72),('profile',72,104),('release',104,136),('loader',136,168),('programdata',168,200),('executable_hash',200,232),('upgrade_authority',232,264),('activation',264,272),('retirement',272,280),('policy',280,312),('bump',312,313),('programdata_bump',313,314),('reserved',314,320)]}
rows=[]
def lit(b):
 return f'List.replicate {len(b)} {b[0]}#u8' if len(set(b))==1 else '['+','.join(f'{n}#u8' for n in b)+']'
for name,fields in layouts.items():
 mod=('JHg_Data' if name in ('Master','Forest') else 'JHb_Data')+name; data=g['images'][name];ns=(len(data)+31)//32
 assert [i for _,a,b in fields for i in range(a,b)]==list(range(len(data))),name
 out=[f'import {mod}','set_option autoImplicit false',f'namespace AspisR1.JHg_Audit{name}','open Aeneas Aeneas.Std Result']
 for field,a,b in fields:
  expected=lit(data[a:b]);out += [f'/-- Frozen layout {name}[{a}:{b}); byte fact, not decoder/native refinement. -/',f'theorem {field} : ({mod}.bytes.drop {a}).take {b-a} = {expected} := by',f'  simp only [{mod}.bytes,'+','.join(f'{mod}.c{i:02}_length' for i in range(ns))+',List.drop_append,List.take_append,List.length_append,Nat.reduceAdd,Nat.reduceSub,Nat.reduceLeDiff,List.length_drop,List.drop_eq_nil_of_le,List.take_of_length_le,List.drop_zero,List.take_zero,List.nil_append,List.append_nil]', '  rfl',f'#print axioms {field}']
  rows.append(dict(account=name,field=field,start=a,end=b,bytes=list(data[a:b]),theorem=f'AspisR1.JHg_Audit{name}.{field}'))
 out += [f'end AspisR1.JHg_Audit{name}'];path=R/f'lean/JHg_Audit{name}.lean';source='\n'.join(out)+'\n'
 if check:assert path.read_text()==source,path
 else:path.write_text(source)
inventory=json.dumps(rows,indent=2)+'\n'
if check:assert (P/'JHg_FIELD_INVENTORY.json').read_text()==inventory
else:(P/'JHg_FIELD_INVENTORY.json').write_text(inventory)
print('fields',len(rows))
