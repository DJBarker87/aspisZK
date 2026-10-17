from pathlib import Path
import hashlib,json
package=Path(__file__).resolve().parents[1];rawpath=package/'evidence/pair-forest-lane-write-extraction-20261017/output/generated/AspisR1PairForestLaneWriteSourceCut/Types.lean';raw=rawpath.read_bytes();sha=lambda b:hashlib.sha256(b).hexdigest();assert sha(raw)=='ebafa89e00d227062b5133725ce4494afbc8bdb722cc084ac3cb52eccdd2873e';s=raw.decode();attr='@[discriminant u8 [1,2]]\n';name='PoolV1TransitionKind';end='| Withdrawal : PoolV1TransitionKind\n';assert s.count(attr)==1 and s.count(end)==1
aux='''
-- Naming-only expansion of the pinned two-code discriminant attribute.
def PoolV1TransitionKind.read_discriminant (x : PoolV1TransitionKind) : U8 :=
  match x with
  | .PrivateTransfer => 1#u8
  | .Withdrawal => 2#u8

instance _root_.AspisR1PairForestLaneWriteSourceCut.PoolV1TransitionKind.instDiscriminant :
    Aeneas.Std.Discriminant PoolV1TransitionKind U8 where
  read_discriminant := PoolV1TransitionKind.read_discriminant
'''
s=s.replace(attr,'').replace(end,end+aux);assert s.replace(aux,'').replace('inductive '+name+' where',attr+'inductive '+name+' where')==raw.decode()
p=package/'lean/AspisR1PairForestLaneWriteSourceCut';p.mkdir(exist_ok=True);(p/'Types.lean').write_text(s);(package/'evidence/terminal-result-constructor-source-20261017/lane-adapter-pins.json').write_text(json.dumps({'raw_types_sha256':sha(raw),'adapted_types_sha256':sha(s.encode()),'source_namespace':'AspisR1PairForestLaneWriteSourceCut','old_instance':'instDiscriminantPoolV1TransitionKindU8','new_instance':'AspisR1PairForestLaneWriteSourceCut.PoolV1TransitionKind.instDiscriminant','constructor_codes':[['PrivateTransfer',1],['Withdrawal',2]],'inverse_recovers_original_bytes':True,'backend_reference':'tools/withdrawal-caller-terminal-discriminant-bridge.py','backend_generator_sha256':'98dca07cb483eda5c4fe4322806650d3288fd0c2504c3153e0cebc195e649d03'},indent=2)+'\n');print(sha(s.encode()))
