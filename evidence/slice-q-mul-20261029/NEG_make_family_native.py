from pathlib import Path
import ast,json,re
E=Path(__file__).resolve().parent
s=(E/'NEG_L054/stdout.log').read_text();values=[]
for m in re.finditer(r'Aeneas.Std.Result.ok\s*\[',s):
 start=s.index('[',m.start());i=start;depth=0
 while True:
  depth+=(s[i]=='[')-(s[i]==']');i+=1
  if depth==0:break
 values.append(ast.literal_eval(s[start:i]))
assert len(values)==3
(E/'NEG_FAMILY_EXPECTED.json').write_text(json.dumps(dict(zip(['prefixes','push','folds'],values)),indent=2)+'\n')
f=json.loads((E/'NEG_FAMILY_FIXTURES.json').read_text())
a=lambda x:str(x).replace(' ','')
code='use super::*;\nfn expected(mut a:Vec<u64>)->Vec<u64>{if std::env::var("NEG_FAMILY_NEGATIVE").is_ok(){a[0]^=1;}a}\n'
code+='#[test] fn NEG_shared_family_prefix(){\n'
for inp,out in zip(f['prefixes'],values[0]):
 code+=f'let input={a(inp)};let (p,t)=batch_prefix_products(&input.map(M31));let mut got:Vec<u64>=p.iter().map(|x|x.0 as u64).collect();got.push(t.0 as u64);assert_eq!(got,expected(vec!{a(out)}));\n'
code+='}\n#[test] fn NEG_shared_family_push(){\n'
for d,out in zip(f['push'],values[1]):
 code+=f'let mut b=BatchedWeights{{raw:vec!{a(d["raw"])},terms:{d["terms"]}}};b.push({d["index"]},super::k({a(d["power"])}),M31({d["basis"]}));let mut got:Vec<u64>=b.raw.iter().flatten().copied().collect();got.push(b.terms as u64);assert_eq!(got,expected(vec!{a(out)}));\n'
code+='}\n#[test] fn NEG_shared_family_folds(){\n'
for d,out in zip(f['folds'],values[2]):
 code+=f'let alpha=E::from_limbs({a(d["alpha"])}).unwrap();let inputs={a(d["a"])}.map(|x|E::from_limbs(x).unwrap());let inverse={a(d["inverse"])}.map(M31);let mut got:Vec<u64>=circle_fold_with_inverses(alpha,inputs,&inverse).to_limbs().iter().map(|x|*x as u64).collect();got.extend(line_fold_with_inverses(alpha,inputs,&inverse).to_limbs().iter().map(|x|*x as u64));assert_eq!(got,expected(vec!{a(out)}));\n'
code+='}\n';(E/'NEG_family_native.rs').write_text(code)
p=E/'NEG_native_tests.rs';t=p.read_text();marker='\n#[path="NEG_family_native.rs"] mod NEG_family_native;\n'
if marker not in t:p.write_text(t+marker)
p=E/'NEG_run.py';t=p.read_text().replace("'NEG_fixture_tests.rs']:files", "'NEG_fixture_tests.rs','NEG_family_native.rs']:files").replace("if os.environ.get('NEG_WRONG'):env", "if os.environ.get('NEG_FAMILY_NEGATIVE'):env['NEG_FAMILY_NEGATIVE']=os.environ['NEG_FAMILY_NEGATIVE']\n    if os.environ.get('NEG_WRONG'):env");p.write_text(t)
