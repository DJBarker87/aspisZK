from pathlib import Path
import re,json,hashlib
E=Path(__file__).resolve().parent;s=(E/'NMX_R3_RegistryEmitted.lean').read_text();body=s[s.index('def body'):s.index('\nend NMX_R3_RegistryEmitted')];body=body.replace('def body','def script',1).replace('  Result (core.result.Result Unit solana_program_error.ProgramError)','  Program (core.result.Result Unit solana_program_error.ProgramError)',1)
lines=body.splitlines();out=[];calls=[];i=0
indent=lambda x:len(x)-len(x.lstrip())
while i<len(lines):
 line=lines[i];txt=line.lstrip();n=indent(line)
 if re.match(r'let \w+ ←',txt):
  head,rhs=line.split('←',1);parts=[]
  if rhs.strip():parts.append(rhs.strip())
  j=i+1
  while j<len(lines) and (not lines[j].strip() or indent(lines[j])>n):parts.append(lines[j].strip());j+=1
  expr=' '.join(parts);tag='scalar'
  dm=re.fullmatch(r'\(r1_pool_adapter\.owned\.OwnedAccount\.data ops\) (\w+)',expr)
  pm=re.fullmatch(r'ops\.op38 (\w+) (\w+)',expr)
  if dm:replacement='data '+dm[1];tag='data'
  elif pm:replacement='pda '+pm[1]+' '+pm[2];tag='pda'
  else:replacement='scalar ('+expr+')'
  out.append(head+'← '+replacement);calls.append(dict(ordinal=len(calls)+1,binder=head.strip(),source_expression=expr,kind=tag));i=j;continue
 if txt.startswith('ok ') or txt=='ok':out.append(' '*n+'pure'+txt[2:]);i+=1;continue
 if txt.startswith('core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual'):
  parts=[txt];j=i+1
  while j<len(lines) and (not lines[j].strip() or indent(lines[j])>n):parts.append(lines[j].strip());j+=1
  out.append(' '*n+'scalar ('+' '.join(parts)+')');i=j;continue
 out.append(line);i+=1
out='\n'.join(out)+'\n';assert len([x for x in calls if x['kind']=='data'])==4;assert len([x for x in calls if x['kind']=='pda'])==6
(E/'NMX_R3_RegistryScript.lean').write_text('import NMX_R3_RegistryProgram\nset_option autoImplicit false\nnoncomputable section\nnamespace NMX_R3_RegistryScript\nopen Aeneas Aeneas.Std Result ControlFlow Error AdapterRw NMX_R3_RegistryProgram\n'+out+'\nend NMX_R3_RegistryScript\nend\n')
(E/'NMX_REGISTRY_SCRIPT_CALLS.json').write_text(json.dumps({'source':'NMX_R3_RegistryEmitted.lean','source_sha256':hashlib.sha256(s.encode()).hexdigest(),'transformation':'every original Result bind is an explicitly classified Command, every terminal ok is Program.ret, terminal residual is a scalar command; no branch, call argument or return payload changes','calls':calls},indent=2)+'\n');print('Emitted',len(calls),'source call occurrences with4 data and6 PDA sites')
