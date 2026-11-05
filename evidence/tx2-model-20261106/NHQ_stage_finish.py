from pathlib import Path
import re
E=Path(__file__).resolve().parent;p=E/'NHQ_FinishRelationModel.lean';s=p.read_text();a=s.index('def staged');b=s.index('theorem source',a);body=s[a:b];definitions=[]
common='(ops : Ops W) (v : verifier.View) (p : verifier.Prepared)\n (a : verifier.Accumulator) (obs : Option (verifier.Phase → Result Unit))'
for tag,reply,ty,extra,renames,call in [
 ('cf4','r4','E','',{},'ops v p a obs r4'),
 ('cf3','r3','E',' (claim : E)',{'val1':'claim'},'ops v p a obs val1 r3'),
 ('cf2','r2','W',' (folds : Usize) (claim : E)',{'i':'folds','val1':'claim'},'ops v p a obs i val1 r2'),
 ('cf1','r1','E',' (folds : Usize)',{'i':'folds'},'ops v p a obs i r1'),
 ('cf','r','E','',{},'ops v p a obs r')]:
 name={'cf4':'afterDotReply','cf3':'afterPairReply','cf2':'afterWeightsReply','cf1':'afterRoundReply','cf':'afterRound0'}[tag]
 lines=body.splitlines(True);idx=next(i for i,l in enumerate(lines) if re.search(r'let '+tag+r' ←',l));indent=len(lines[idx])-len(lines[idx].lstrip());end=idx+1
 while end<len(lines) and (not lines[end].strip() or len(lines[end])-len(lines[end].lstrip())>=indent):end+=1
 frag=''.join(l[indent:] if l.strip() else l for l in lines[idx:end]);renames={reply:'reply',**renames}
 for x,y in renames.items():frag=re.sub(r'\b'+x+r'\b',y,frag)
 definitions.append('def '+name+' '+common+extra+'\n (reply : R '+ty+') : Result (R Unit) := do\n'+''.join(' '+l if l.strip() else l for l in frag.splitlines(True)))
 lines[idx:end]=[' '*indent+name+' '+call+'\n'];body=''.join(lines)
s=s[:a]+'\n'.join(definitions)+'\n'+body+s[b:];p.write_text(s)
