#!/usr/bin/env python3
"""Static command spans for handwritten Lean; never invokes Lean.

Unlike the generated-declaration parser, theorem and context commands terminate
preceding definitions. Context syntax is preserved for inverse review. This is
not elaboration or a claim that inferred instance/implicit arguments agree.
"""
import re,hashlib
DECL=re.compile(r'(?m)^(?:(?:@\[[^\n]*\])[ \t]*(?:\n[ \t]*)?)*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*(def|abbrev|theorem|lemma|structure|inductive|instance|axiom|opaque)\b[^\n]*')
CONTEXT=re.compile(r'(?m)^(?:(?:noncomputable\s+)?section\b|namespace\b|end\b|variable\b|universe\b|open\b|attribute\b|set_option\b|include\b|omit\b|export\b|local notation\b|notation\b|syntax\b|macro\b|#print\b|#check\b)[^\n]*')
sha=lambda b:hashlib.sha256(b).hexdigest()
def commands(text,tokenize,canonical):
 events=sorted([(m.start(),m.end(),'declaration',m) for m in DECL.finditer(text)]+[(m.start(),m.end(),'context',m) for m in CONTEXT.finditer(text)])
 # A regex match inside a multiline comment is not a command. Preserve offsets
 # and erase only comments before deciding whether each command is visible.
 visible=list(text);i=depth=0
 while i<len(text):
  if text[i:i+2]=='/-':depth+=1;visible[i:i+2]='  ';i+=2
  elif depth and text[i:i+2]=='-/':depth-=1;visible[i:i+2]='  ';i+=2
  elif depth:
   if text[i]!='\n':visible[i]=' '
   i+=1
  elif text[i:i+2]=='--':
   j=text.find('\n',i);j=len(text) if j<0 else j
   visible[i:j]=' '*(j-i);i=j
  else:i+=1
 v=''.join(visible);events=[e for e in events if v[e[0]:e[1]].strip()]
 result={};history=[];scopes=[];transient=[]
 for idx,(start,_,kind,match) in enumerate(events):
  end=events[idx+1][0] if idx+1<len(events) else len(text)
  raw=text[start:end];tokens=tokenize(raw)
  if kind=='context':
   if not tokens:continue
   command=canonical(tokens).decode();history.append({'tokens':tokens,'token_sha256':sha(canonical(tokens)),'line':text[:start].count('\n')+1})
   head=tokens[0]
   if head=='namespace':scopes.append({'kind':'namespace','name':''.join(tokens[1:])})
   elif head=='section' or tokens[:2]==['noncomputable','section']:scopes.append({'kind':'section','name':''.join(tokens[1:] if head=='section' else tokens[2:])})
   elif head=='end':
    if scopes:scopes.pop()
   if head=='open' and tokens[-1:] == ['in']:transient.append(tokens)
   continue
  if not tokens:continue
  # Attributes/modifiers precede the declaration keyword.
  k=next(i for i,t in enumerate(tokens) if t in ['def','abbrev','theorem','lemma','structure','inductive','instance','axiom','opaque'])
  declkind=tokens[k];name=tokens[k+1] if k+1<len(tokens) else '@anonymous'
  if declkind=='instance' and name in [':','{','[','(']:name='@instance:'+str(text[:start].count('\n')+1)
  if name in result:raise ValueError(('ambiguous lexical declaration',name))
  delimiter=next((j for j in range(k+1,len(tokens)) if tokens[j] in [':=','where','|']),len(tokens))
  ns='.'.join(x['name'] for x in scopes if x['kind']=='namespace')
  result[name]={'kind':declkind,'qualified_name':(ns+'.' if ns else '')+name,'start_byte':len(text[:start].encode()),'end_byte_exclusive':len(text[:end].encode()),'start_line':text[:start].count('\n')+1,'end_line':text[:end-1].count('\n')+1,
   'raw_segment_sha256':sha(raw.encode()),'declaration_token_sha256':sha(canonical(tokens)),'signature_tokens':tokens[:delimiter],'signature_token_sha256':sha(canonical(tokens[:delimiter])),
   'active_scope_syntax':list(scopes),'context_command_history':list(history),'context_command_history_sha256':sha(canonical([t for c in history for t in c['tokens']])),'immediately_preceding_transient_context':list(transient),
   'scope_limit':'Static source command/context syntax only. Inferred binders, private-name mangling, generated instances and elaboration equality remain unchecked.'}
  transient=[]
 return result
