#!/usr/bin/env python3
"""Additional two-code naming expansion for the Terminal/Caller joint import."""
from pathlib import Path
import argparse,hashlib,json
base=Path(__file__).resolve().parents[1]
source=base/'lean/bridge-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Types.lean'
dest=base/'lean/bridge-withdrawal-caller-terminal-20261016/AspisR1WithdrawalCaller/Types.lean'
pins=dest.parent.parent/'adapter-pins.json';sha=lambda b:hashlib.sha256(b).hexdigest()
raw=source.read_bytes();assert sha(raw)=='ed3c8ec36f16837ba48e741a7dc93bfd870c338762574e420b2105c6cfcb8b24'
s=raw.decode();attr='@[discriminant u8 [1,2]]\n';assert s.count(attr)==1
E='pool_v1.historical_anchor.PoolV1TransitionKind';end='| Withdrawal : '+E+'\n';assert s.count(end)==1
aux='\n-- Naming-only expansion of the pinned two-code discriminant attribute.\ndef '+E+'.read_discriminant (x : '+E+') : U8 :=\n  match x with\n  | .PrivateTransfer => 1#u8\n  | .Withdrawal => 2#u8\n\ninstance _root_.AspisR1WithdrawalCaller.'+E+'.instDiscriminant :\n    Aeneas.Std.Discriminant '+E+' U8 where\n  read_discriminant := '+E+'.read_discriminant\n'
adapted=s.replace(attr,'').replace(end,end+aux)
assert adapted.replace(aux,'').replace('inductive '+E+' where',attr+'inductive '+E+' where')==s
record={'input_source':str(source.relative_to(base)),'input_sha256':sha(raw),'output_source':str(dest.relative_to(base)),'output_sha256':sha(adapted.encode()),'original_generated_source':'lean/extracted-withdrawal-caller-20261016/AspisR1WithdrawalCaller/Types.lean','original_generated_sha256':'c4ca66305b9b9f3bd30fc854b5ddc18d69d6a9f6ed22f939efc788471b6e90c7','prior_error_adapter_unchanged':True,'backend_generator_source':'Aeneas/Data/Discriminant.lean','backend_generator_sha256':'98dca07cb483eda5c4fe4322806650d3288fd0c2504c3153e0cebc195e649d03','old_instance':'instDiscriminantPoolV1TransitionKindU8','new_instance':'AspisR1WithdrawalCaller.'+E+'.instDiscriminant','constructor_codes':[['PrivateTransfer',1],['Withdrawal',2]],'inverse_recovers_input_bytes':True}
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
if args.check:
 assert dest.read_text()==adapted and json.loads(pins.read_text())==record
 print('PASS: all input bytes recovered by inverse; only two-code Kind instance identity changes')
else:
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(adapted);pins.write_text(json.dumps(record,indent=2)+'\n');print(dest)
