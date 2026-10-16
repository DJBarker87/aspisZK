#!/usr/bin/env python3
"""Names-only expansion of all five common-module discriminant instances."""
from pathlib import Path
import argparse,hashlib,json,re,subprocess
base=Path(__file__).resolve().parents[1]
source=base/'lean/extracted-public-preparation-20261016/AspisR1PublicPreparation/Types.lean'
expected='88b760f734fc7cc23ad36992894f4b5cb38f3d3b7f82d53dd631ca70c73e9eee'
dest=base/'lean/bridge-public-preparation-20261016/AspisR1PublicPreparation/Types.lean'
pins=dest.parent.parent/'adapter-pins.json'
sha=lambda b:hashlib.sha256(b).hexdigest()
errors=[('Allocation',0),('RowOrder',2),('InvalidRow',0),('Tag',1),('Length',1),
 ('NonCanonical',2),('Boundary',1),('Terminal',0),('EqualCirclePoints',0),('TrailingBytes',0),('Public',0)]
items=[('aspis_core.state_only_prefix.r0.Error',errors),
 ('pool_v1.pair_forest_terminal.PoolV1PairForestTerminalStatementV1',[('PrivateTransfer',2),('Withdrawal',2)]),
 ('pool_v1.pair_forest_semantic_terminal.r0.Public',[('Transfer',2),('Withdrawal',2)]),
 ('pool_v1.pair_forest_semantic_terminal.CompiledVariant',[('PrivateTransfer',0),('Withdrawal',0)]),
 ('r1_wire.Error',errors)]
def adapt(raw):
 assert sha(raw)==expected
 s=raw.decode();original=s;replacements=[];records=[]
 for name,ctors in items:
  marker='@[discriminant isize]\ninductive '+name
  assert s.count(marker)==1,name
  start=s.index(marker);end=s.index('\n\n',start)
  body=s[start:end]
  assert re.findall(r'^\| (\w+)',body,re.M)==[n for n,_ in ctors],name
  aux='\n\n-- Naming-only expansion: same constructor order, same generated reader.\n'
  aux+='def '+name+'.read_discriminant (x : '+name+') : Isize :=\n  match x with\n'
  aux+=''.join('  | .'+ctor+(' _'*arity)+' => '+str(i)+'#isize\n' for i,(ctor,arity) in enumerate(ctors))
  aux+='\ninstance _root_.AspisR1PublicPreparation.'+name+'.instDiscriminant :\n'
  aux+='    Aeneas.Std.Discriminant '+name+' Isize where\n'
  aux+='  read_discriminant := '+name+'.read_discriminant'
  replacement=body.replace('@[discriminant isize]\n','',1)+aux
  assert s.count(body)==1;s=s.replace(body,replacement,1)
  replacements.append((body,replacement))
  records.append({'type':name,'constructor_codes':[[c,i] for i,(c,_) in enumerate(ctors)],
   'new_instance':'AspisR1PublicPreparation.'+name+'.instDiscriminant'})
 inverse=s
 for old,new in reversed(replacements):
  assert inverse.count(new)==1;inverse=inverse.replace(new,old,1)
 assert inverse==original and s.count('@[discriminant isize]')==0
 return s.encode(),records
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--source',type=Path,default=source)
 ap.add_argument('--revision',required=True);ap.add_argument('--check',action='store_true');a=ap.parse_args()
 raw=a.source.read_bytes()
 tracked=subprocess.check_output(['git','show',a.revision+':docs/research/100bit-spend-path-20261013/'+str(source.relative_to(base))],cwd=base)
 assert raw==tracked
 out,records=adapt(raw)
 record={'original_revision':a.revision,'original_source':str(source.relative_to(base)),
  'original_sha256':sha(raw),'adapter_source':str(dest.relative_to(base)),'adapter_sha256':sha(out),
  'generator_source':'Aeneas/Data/Discriminant.lean',
  'generator_sha256':'98dca07cb483eda5c4fe4322806650d3288fd0c2504c3153e0cebc195e649d03',
  'rule':'Pinned generator maps constructors in order and emits an anonymous instance. Only instance identities are qualified; reader definitions and constructor types are unchanged.',
  'observed_collision':'instDiscriminantErrorIsize between original common and old serializer Types',
  'predicted_collisions':'Other Error, Public, CompiledVariant and TerminalStatement are source-predicted until comprehensive joint import.',
  'instances':records,'constructor_tags':28,'inverse_recovers_original_bytes':True,
  'original_Funs_unchanged_sha256':'d4b77a8657f3356079268735d02e225a37b61246c3f43782781f82a3dd05fde3'}
 if a.check:assert dest.read_bytes()==out and json.loads(pins.read_text())==record
 else:
  dest.parent.mkdir(parents=True,exist_ok=True);dest.write_bytes(out)
  pins.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
 print(json.dumps({'checked':a.check,'tags':28,'inverse':True,'adapter_sha256':sha(out)}))
if __name__=='__main__':main()
