from pathlib import Path
import re,json
E=Path(__file__).resolve().parent
# Top-level arrows only: function arguments may themselves be callbacks.
def arrows(s):
 out=[];depth=0;start=0
 for i,c in enumerate(s):
  depth+=(c in '({[')-(c in ')}]')
  if c=='→' and depth==0:out.append(s[start:i].strip());start=i+1
 out.append(s[start:].strip());return out
def declaration(sig):
 depth=0;colon=None
 for i,c in enumerate(sig):
  depth+=(c in '({[')-(c in ')}]')
  if c==':' and depth==0:colon=i;break
 assert colon is not None
 return sig[:colon].strip(),sig[colon+1:].strip()
def boundnames(b):
 out=[];depth=0;start=0
 for i,c in enumerate(b):
  if c in '({[':
   if depth==0:start=i
   depth+=1
  elif c in ')}]':
   depth-=1
   if depth==0:
    m=re.match(r'[({]\s*([^ :]+)\s*:',b[start:i+1])
    if m:out.append(m[1])
 return out
for fn,root,row in [('tx1','verifier.candidate.tx1','094'),('first','first_decoded','328'),('stage1_owned','r1_pool_adapter.owned.stage1_owned','345')]:
 s=(E/f'NMT_{fn}.Funs.lean').read_text();mapping=json.loads((E/'NMT_lean'/('NMT_'+fn)/'NMT_PARAMETERS.json').read_text())
 start=s.index('def '+root);roottext=s[start:s.index('\nend NMT_',start)];split=roottext.index(':= do');sig=roottext[:split];body=roottext[split+len(':= do'):]
 # first_decoded is followed by first's independent definitions, exclude them.
 if '\n/--' in body:body=body[:body.index('\n/--')]
 wrappers=[];text=f'import NMT_{fn}.Funs\nimport NMT_CallTree\nset_option autoImplicit false\nnoncomputable section\nnamespace NMT_{fn}\nopen Aeneas Aeneas.Std Result\nopen AspisR1.NMT_CallTree\n'
 for m in mapping:
  call=m['parameter']
  if not re.search(r'\b'+call+r'\b',sig):continue
  bind,ty=declaration(m['signature']);parts=arrows(' '.join(ty.split()));ret=parts[-1];assert ret.startswith('Result '),(call,ret)
  wrap='NMT_'+row+'_'+call;wrappers.append(wrap)
  originaltype=('∀ '+bind+', ' if bind else '')+ty
  args=parts[:-1];names=boundnames(bind);actual=[x for x in names if not re.search(r'\{\s*'+re.escape(x)+r'\s*:',bind)]
  # Generic H is implicit, trait D is explicit. All observed values are retained.
  more=[f'a{i}' for i in range(len(args))];actual+=more
  applied=call+(' '+' '.join(actual) if actual else '')
  argtuple='('+','.join(actual)+')' if len(actual)>1 else actual[0] if actual else '()'
  text+=f'def {wrap} ({call} : {originaltype}) {bind} '+''.join(f'({x} : {t}) ' for x,t in zip(more,args))+f': Code {ret[len("Result "):]} :=\n invoke {json.dumps(m["generated_name"])} {argtuple} ({applied})\n'
  body=re.sub(r'(?m)(^\s*|←\s*)'+re.escape(call)+r'\b',lambda z:z[1]+'('+wrap+' '+call+')',body)
 # Lift the SAME raw std calls; child calls record their exact typed tuples.
 body=re.sub(r'\bok\b','pure',body)
 # Mark the root result only; child parameters remain actual Result functions.
 at=sig.index('\n  {H : Type}') if fn=='tx1' else sig.index('\n  (public1') if fn=='first' else sig.index('\n  (program_id')
 tail=sig[at:];idx=tail.rindex('Result (core.result.Result');tail=tail[:idx]+'Code (core.result.Result'+tail[idx+len('Result (core.result.Result'):]
 reified=sig[:at].replace('def '+root,'def NMT_'+row+'_tree',1)+tail
 text+=reified+':= do'+body+'\n'
 # Preserve original argument binder signature for the erasure theorem.
 headers=sig[:at].replace('def '+root,'theorem NMT_'+row+'_erase',1);inputs=sig[at:sig.rfind(':\n')]
 # Binder names in final argument segment; H/D is in input segment for tx1.
 own=boundnames(inputs);own=[x for x in own if not re.search(r'\{\s*'+re.escape(x)+r'\s*:',inputs)]
 params=[m['parameter'] for m in mapping if re.search(r'\b'+m['parameter']+r'\b',sig)]
 apply=' '.join(params+own)
 text+=headers+inputs+f':\n erase (NMT_{row}_tree {apply}) = {root} {apply} := by\n'
 text+=' unfold NMT_'+row+'_tree '+root+'\n'
 laws='[Bind.bind, Pure.pure, MonadLift.monadLift, AspisR1.NMT_CallTree.bind,erase,invoke, erase_bind,erase_lift,erase_pure,erase_invoke,result_right,result_assoc,'+','.join(wrappers)+']'
 text+=' simp only '+laws+'\n'
 text+=" repeat' first\n | rfl\n | (split <;> simp only "+laws+")\n | (congr 1 <;> first | rfl | (funext x; simp only "+laws+"))\n"
 text+='#print axioms NMT_'+row+'_erase\nend NMT_'+fn+'\n'
 (E/f'NMT_{row}Tree.lean').write_text(text)
