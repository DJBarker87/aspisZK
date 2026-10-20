#!/usr/bin/env python3
"""Normalize only generated discriminant registrations to qualified names."""
from pathlib import Path
import argparse,json,re,hashlib
ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
tool=Path(__file__).resolve().parent;area=tool.parents[1];records=[]
for ns,sub in [('AspisR1CanonicalReader','canonical-reader'),('AspisR1CanonicalKReader','canonical-kreader')]:
 raw=(tool/(sub+'-generated')/'Types.lean').read_text()
 marker='@[discriminant isize]\n';assert raw.count(marker)==1
 begin=raw.index(marker);end=raw.index('\n/--',begin)
 enum=raw[begin:end];names=re.findall(r'^\| (\w+) : Error$',enum,re.M)
 assert names==['Parse','Semantic','Transcript','Relation','Merkle','Query','Checkpoint','Allocation']
 regs='\ndef Error.read_discriminant : Error → Isize\n'+''.join(f'  | .{name} => {i}#isize\n' for i,name in enumerate(names))
 regs+=f'instance _root_.{ns}.Error.instDiscriminant :\n    Aeneas.Std.Discriminant Error Isize where\n  read_discriminant := Error.read_discriminant\n'
 types=raw[:begin]+enum.replace(marker,'')+regs+raw[end:]
 # Inverse strips exactly the explicit registration, restoring original macro annotation.
 assert types.replace(regs,'').replace('inductive Error where',marker+'inductive Error where',1)==raw
 p=area/'lean'/ns/'Types.lean'
 if args.check:assert p.read_text()==types,ns
 else:p.write_text(types)
 records.append(dict(namespace=ns,raw_types_sha256=hashlib.sha256(raw.encode()).hexdigest(),installed_types_sha256=hashlib.sha256(types.encode()).hexdigest(),constructors=names,ordinals=list(range(8)),normalization='Discriminant instance registration fully qualified; constructor declarations/order and ordinal read_discriminant body unchanged'))
p=tool/'canonical-readers-emission.json';data=json.dumps(records,indent=2)+'\n'
if args.check:assert p.read_text()==data
else:p.write_text(data)
print(json.dumps(dict(check=args.check,registration_name_only=True,readers=2)))
