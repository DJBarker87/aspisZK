#!/usr/bin/env python3
"""One-sided naming adapter, following prefix-discriminant-bridge.py (36dd8dc0a)."""
from pathlib import Path
import argparse,hashlib,json
base=Path(__file__).resolve().parents[1]
source=base/'lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Types.lean'
dest=base/'lean/bridge-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Types.lean'
pins=dest.parent.parent/'adapter-pins.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
raw=source.read_bytes();assert sha(raw)=='c4ca66305b9b9f3bd30fc854b5ddc18d69d6a9f6ed22f939efc788471b6e90c7'
s=raw.decode();attr='@[discriminant isize]\n';assert s.count(attr)==1
E='pool_v1.payment_relation.PoolV1PaymentStatementFormatError'
ctors=['WrongLength','WrongMagic','WrongVersion','WrongTransitionKind','WrongDigestEncoding','NonZeroReserved','ZeroRequiredBinding','InvalidAnchorSequence','NonCanonicalDigest','NonCanonicalAssetId','InvalidWithdrawalAmount','InvalidDestination','InvalidEnvelope','EnvelopeMismatch']
end='| EnvelopeMismatch : '+E+'\n';assert s.count(end)==1
aux='\n-- Naming-only expansion of the pinned discriminant attribute.\ndef '+E+'.read_discriminant (x : '+E+') : Isize :=\n  match x with\n'+''.join(f'  | .{c} => {i}#isize\n' for i,c in enumerate(ctors))+'\ninstance _root_.AspisR1WithdrawalCaller.'+E+'.instDiscriminant :\n    Aeneas.Std.Discriminant '+E+' Isize where\n  read_discriminant := '+E+'.read_discriminant\n'
adapted=s.replace(attr,'').replace(end,end+aux)
assert adapted.replace(aux,'').replace('inductive '+E+' where',attr+'inductive '+E+' where')==s
record={'original_source':str(source.relative_to(base)),'original_sha256':sha(raw),'adapter_source':str(dest.relative_to(base)),'adapter_sha256':sha(adapted.encode()),'backend_generator_source':'Aeneas/Data/Discriminant.lean','backend_generator_sha256':'98dca07cb483eda5c4fe4322806650d3288fd0c2504c3153e0cebc195e649d03','method_reference':'prefix-discriminant-bridge.py at36dd8dc0a','generator_rule':'constructor order mapIdx; same read_discriminant; only generated instance name qualified','old_instance':'instDiscriminantPoolV1PaymentStatementFormatErrorIsize','new_instance':'AspisR1WithdrawalCaller.'+E+'.instDiscriminant','constructor_codes':[[c,i] for i,c in enumerate(ctors)],'original_source_unchanged':True}
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
if args.check:
 assert dest.read_text()==adapted and json.loads(pins.read_text())==record
 print('PASS: all original bytes recovered by inverse; only Error instance identity changes')
else:
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(adapted);pins.write_text(json.dumps(record,indent=2)+'\n');print(dest)
