#!/usr/bin/env python3
"""One-sided naming adapter for the actual Terminal/public joint import."""
from pathlib import Path
import argparse,hashlib,json,subprocess
base=Path(__file__).resolve().parents[1]
relative='docs/research/100bit-spend-path-20261013/lean/extracted-terminal-validator-20261016/AspisR1TerminalValidator/Types.lean'
revision='ddcaa068e2d964a09b69ea204e54bc000402364a'
source=base/'lean/extracted-terminal-validator-20261016/AspisR1TerminalValidator/Types.lean'
raw=source.read_bytes() if source.exists() else subprocess.check_output(['git','show',revision+':'+relative],cwd=base)
sha=lambda b:hashlib.sha256(b).hexdigest()
assert sha(raw)=='5ac27c38f74aa4cbeb7ad1c224ae0cf9fa324458f591f8ee57604371b8f01d7e'
dest=base/'lean/bridge-terminal-public-20261016/AspisR1TerminalValidator/Types.lean';pins=dest.parent.parent/'adapter-pins.json'
s=raw.decode();attr='@[discriminant isize]\n';E='pool_v1.payment_relation.PoolV1PaymentStatementFormatError';marker=attr+'inductive '+E+' where';assert s.count(marker)==1
ctors=['WrongLength','WrongMagic','WrongVersion','WrongTransitionKind','WrongDigestEncoding','NonZeroReserved','ZeroRequiredBinding','InvalidAnchorSequence','NonCanonicalDigest','NonCanonicalAssetId','InvalidWithdrawalAmount','InvalidDestination','InvalidEnvelope','EnvelopeMismatch']
end='| EnvelopeMismatch : '+E+'\n';assert s.count(end)==1
aux='\n-- Naming-only expansion of the pinned fourteen-code discriminant attribute.\ndef '+E+'.read_discriminant (x : '+E+') : Isize :=\n  match x with\n'+''.join(f'  | .{c} => {i}#isize\n' for i,c in enumerate(ctors))+'\ninstance _root_.AspisR1TerminalValidator.'+E+'.instDiscriminant :\n    Aeneas.Std.Discriminant '+E+' Isize where\n  read_discriminant := '+E+'.read_discriminant\n'
adapted=s.replace(marker,'inductive '+E+' where').replace(end,end+aux)
assert adapted.replace(aux,'').replace('inductive '+E+' where',marker)==s
record={'original_source':relative,'original_revision':revision,'original_sha256':sha(raw),'adapter_source':str(dest.relative_to(base)),'adapter_sha256':sha(adapted.encode()),'backend_generator_source':'Aeneas/Data/Discriminant.lean','backend_generator_sha256':'98dca07cb483eda5c4fe4322806650d3288fd0c2504c3153e0cebc195e649d03','generator_rule':'constructor order mapIdx; same read_discriminant; only generated instance name qualified','old_instance':'instDiscriminantPoolV1PaymentStatementFormatErrorIsize','new_instance':'AspisR1TerminalValidator.'+E+'.instDiscriminant','constructor_codes':[[c,i] for i,c in enumerate(ctors)],'inverse_recovers_original_bytes':True,'all_other_attributes_unchanged':True}
p=argparse.ArgumentParser();p.add_argument('--check',action='store_true');args=p.parse_args()
if args.check:
 assert dest.read_text()==adapted and json.loads(pins.read_text())==record
 print('PASS: original bytes recovered by inverse; only payment Error instance identity changes')
else:
 dest.parent.mkdir(parents=True,exist_ok=True);dest.write_text(adapted);pins.write_text(json.dumps(record,indent=2)+'\n');print(dest)
