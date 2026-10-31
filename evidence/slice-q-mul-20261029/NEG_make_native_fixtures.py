from pathlib import Path
import json,ast,hashlib
E=Path(__file__).resolve().parent
receipt=json.loads((E/'NEG_L033/receipt.json').read_text());assert receipt['exit_status']==0
s=(E/'NEG_L033/stdout.log').read_text();values=[]
for part in s.split('Aeneas.Std.Result.ok')[1:]:
 start=part.index('[');depth=0
 for j in range(start,len(part)):
  if part[j]=='[':depth+=1
  elif part[j]==']':
   depth-=1
   if depth==0:values.append(ast.literal_eval(part[start:j+1]));break
assert len(values)==2
inputs=json.loads((E/'NEG_FIXTURES.json').read_text());rows,dots=values
assert len(rows)==len(inputs['rows']) and len(dots)==4*len(inputs['dots'])
(E/'NEG_EXPECTED.json').write_text(json.dumps(dict(lean_attempt='NEG_L033',source_sha256=receipt['source_hashes'],stdout_sha256=hashlib.sha256((E/'NEG_L033/stdout.log').read_bytes()).hexdigest(),rows=rows,dots=dots),indent=2)+'\n')
arr=lambda a:'['+','.join(map(str,a))+']'
t='// Expected values are exact successful NEG_L033 emitted-model evaluations.\n'
t+='#[test] fn NEG_shared_rows(){\n'
for i,(r,e) in enumerate(zip(inputs['rows'],rows)):
 t+=f"{{let mut row:[u64;4]={arr(r['raw'])};update_residue_row(&mut row,k({arr(r['power'])}),M31({r['basis']}),{str(r['flush']).lower()});let mut expected:[u64;4]={arr(e)};if std::env::var_os(\"NEG_FIXTURE_NEGATIVE\").is_some(){{expected[0]^=1;}}assert_eq!(row,expected,\"shared row {i}\");}}\n"
t+='println!("NEG_shared_rows emitted_model_cases=24");}\n#[test] fn NEG_shared_dots(){\n'
for i,d in enumerate(inputs['dots']):
 t+='{let q:[u8;608]='+arr(d['q'])+';let g:[E;29]=['+','.join('E::from_limbs('+arr(g)+').unwrap()' for g in d['g'])+'];let out=fast_dots::four_dots(&q,&g);\n'
 for slot in range(4):
  t+=f"{{let mut expected:[u32;8]={arr(dots[4*i+slot])};if std::env::var_os(\"NEG_FIXTURE_NEGATIVE\").is_some(){{expected[0]^=1;}}assert_eq!(out[{slot}].to_limbs(),expected,\"shared dots {i} slot {slot}\");}}\n"
 t+='}\n'
t+='println!("NEG_shared_dots emitted_model_slots=24");}\n'
(E/'NEG_fixture_tests.rs').write_text(t)
