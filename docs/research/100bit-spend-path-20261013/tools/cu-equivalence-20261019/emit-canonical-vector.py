from pathlib import Path
import re
import argparse,json
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;base=tool.parents[1];raw=tool/'canonical-vector-generated';old=tool/'canonical-dots-generated/Types.lean';newtypes=(raw/'Types.lean').read_text();oldtypes=old.read_text();blocks=re.findall(r'/--[\s\S]*?(?=\n/--|\nend AspisR1CanonicalDots)',newtypes)
keep=[]
for b in blocks:
 m=re.search(r'^(?:def|structure|inductive) ([\w.]+)',b,re.M)
 if not m:continue
 n=m.group(1)
 if n=='Error' or n.startswith(('old_callers.','new_callers.')):keep.append(b)
 else:
  decl=b[b.index('\n',b.index('-/'))+1:]
  assert decl.strip() in oldtypes,(n,decl)
head='import AspisR1CanonicalDots.Types\nopen Aeneas Aeneas.Std Result ControlFlow\nnamespace AspisR1CanonicalDots\n'
types=head+'\n'.join(keep)+'\nend AspisR1CanonicalDots\n#print axioms AspisR1CanonicalDots.Error\n'
types=types.replace('@[discriminant isize]\n','')
i=types.index('\n/-- [aspis_canonical_vector_callers::new_callers')
regs="""
def Error.read_discriminant : Error→Isize
  | .Parse => 0#isize
  | .Semantic => 1#isize
  | .Transcript => 2#isize
  | .Relation => 3#isize
  | .Merkle => 4#isize
  | .Query => 5#isize
  | .Checkpoint => 6#isize
  | .Allocation => 7#isize
instance _root_.AspisR1CanonicalDots.Error.instDiscriminant :
    Aeneas.Std.Discriminant Error Isize where
  read_discriminant := Error.read_discriminant
"""
types=types[:i]+regs+types[i:]
outputs={'CanonicalVectorTypes.lean':types}
s=(raw/'Funs.lean').read_text().replace('import AspisR1CanonicalDots.Types','import CanonicalVectorTypes').replace('import AspisR1CanonicalDots.FunsExternal','import CanonicalVectorExternal').replace('namespace AspisR1CanonicalDots\n','namespace AspisR1CanonicalDots\nvariable [Shared] [VectorCommon]\n',1)
outputs['CanonicalVectorSource.lean']=s+'\n#print axioms AspisR1CanonicalDots.old_callers.claim_dot\n#print axioms AspisR1CanonicalDots.new_callers.claim_dot\n#print axioms AspisR1CanonicalDots.old_callers.tail\n#print axioms AspisR1CanonicalDots.new_callers.tail\n'
for name,text in outputs.items():
 target=base/'lean'/name
 if args.check:assert target.read_text()==text,name
 else:target.write_text(text)
# The sole new standard primitive repeats the exact already admitted source body.
pin=base/'lean/extracted-public-preparation-c16-20261019/AspisR1PublicPreparation/Funs.lean'
text=pin.read_text();start=text.index('def core.result.Result.map_err');end=text.index('\n/--',start)
assert text[start:end].strip() in (base/'lean/CanonicalVectorExternal.lean').read_text()
print(json.dumps(dict(check=args.check,shared_types_partition_checked=True,raw_function_bodies_unchanged=True,discriminant_registration_name_only=True,exact_existing_map_err_body=True)))
