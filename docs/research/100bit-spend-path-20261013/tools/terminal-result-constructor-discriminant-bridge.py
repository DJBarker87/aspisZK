from pathlib import Path
import hashlib,json
package=Path(__file__).resolve().parents[1];base=package/'evidence/terminal-result-constructor-source-20261017/raw-generated/AspisR1TerminalResultConstructorCut';raw=(base/'Types.lean').read_bytes();s=raw.decode();sha=lambda b:hashlib.sha256(b).hexdigest();assert sha(raw)=='2c708aa5a76d5a55778bcb93ebd493e93a2b85716c02d23424386ca0c61e8a01'
changes=[]
for attr,name,ty,branches,end in [
 ('@[discriminant u8 [1,2]]\n','PoolV1TransitionKind','U8',[('PrivateTransfer','1#u8'),('Withdrawal','2#u8')],'| Withdrawal : PoolV1TransitionKind\n'),
 ('@[discriminant isize]\n','PoolV1PairForestTerminalStatementV1','Isize',[('PrivateTransfer _ _','0#isize'),('Withdrawal _ _','1#isize')],'| Withdrawal :\n  PoolV1PairForestTerminalCommonV1 →\n  PoolV1WithdrawalPublicV1 →\n  PoolV1PairForestTerminalStatementV1\n')]:
 marker=attr+'inductive '+name+' where';assert s.count(marker)==1 and s.count(end)==1
 aux='\n-- Naming-only expansion of the pinned Aeneas discriminant attribute.\ndef '+name+'.read_discriminant (x : '+name+') : '+ty+' :=\n  match x with\n'+''.join('  | .'+c+' => '+v+'\n' for c,v in branches)+'\ninstance _root_.AspisR1TerminalResultConstructorCut.'+name+'.instDiscriminant :\n    Aeneas.Std.Discriminant '+name+' '+ty+' where\n  read_discriminant := '+name+'.read_discriminant\n'
 s=s.replace(marker,'inductive '+name+' where').replace(end,end+aux);changes.append((marker,name,aux))
inverse=s
for marker,name,aux in reversed(changes):inverse=inverse.replace(aux,'').replace('inductive '+name+' where',marker)
assert inverse==raw.decode()
o=package/'lean/AspisR1TerminalResultConstructorCut';o.mkdir(parents=True,exist_ok=True);(o/'Types.lean').write_text(s);(o/'Funs.lean').write_bytes((base/'Funs.lean').read_bytes());(package/'evidence/terminal-result-constructor-source-20261017/adapter-pins.json').write_text(json.dumps({'raw_types_sha256':sha(raw),'adapted_types_sha256':sha(s.encode()),'funs_sha256':sha((base/'Funs.lean').read_bytes()),'rule':'Expand exact generated discriminant readers, qualify only instance names to avoid global collision. Types/constructor order/codes preserved, inverse recovers original generated Types byte for byte.','backend_reference':'tools/withdrawal-caller-terminal-discriminant-bridge.py','backend_source_sha256':'98dca07cb483eda5c4fe4322806650d3288fd0c2504c3153e0cebc195e649d03','instances':[{'type':n,'instance':'AspisR1TerminalResultConstructorCut.'+n+'.instDiscriminant'} for _,n,_ in changes]},indent=2)+'\n');print(sha(s.encode()))
