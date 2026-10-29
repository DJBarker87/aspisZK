"""Factor the unchanged emitted digest body at top-level monadic stage boundaries.
Only syntax factoring: each emitted stage is retained literally, and the kernel
checks a separate defining equation and the final factorization equation.
"""
from pathlib import Path
import re,sys,json,hashlib
D=Path('evidence/pv-b3p6-20261028');L=D/'lean';s=(L/'PV_B3P_P227_11.lean').read_text();body=s.split('  := do\n',1)[1].split('\n\n\nend ',1)[0]
lines=body.splitlines();starts=[0]
# New stage starts immediately after each top-level digest bind, before the next action.
for i,line in enumerate(lines):
 if i and re.match(r'  let (?:i2|digests3|i4|block(?:[1-9][0-9]*)?|i46) (?:←|:=)',line):
  # i4 also occurs at the change stage only (recipient's i4 is indented six).
  starts.append(i)
starts=sorted(set(starts));chunks=['\n'.join(lines[a:b]) for a,b in zip(starts,starts[1:]+[len(lines)])]
# Assert exact expected 25 independent stages: 4 initial,20 frontier,1 tail.
assert len(chunks)==25,(len(chunks),[x.splitlines()[0]for x in chunks])
header='''namespace PV_B3P_Success227
open Aeneas Aeneas.Std PV_B3P_227
set_option autoImplicit false
abbrev Digest8Q := Array aspis_core.field.QM31 8#usize
'''
params='''(public1 : reference_terminal.SemanticPublic)
    (openings : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings)
    (selectors : reference_copy_terminal.Selectors)'''
fields={'anchor':'anchor','nullifier':'nullifier','recipient':'recipient','change':'change','index':'transition.live_snapshot.next_pair_index','frontier':'transition.live_snapshot.frontier','next_root':'transition.candidate_afterstate.next_root','next_frontier':'transition.candidate_afterstate.next_frontier'}
out=['import PV_B3P_SemanticCallersSuccess227\nimport PV_B3P_CarrySuccess227\nimport PV_B3P_PublicSuccess227\n'+header]
for name,path in fields.items():
 # This is a projection only; RHS retains valid_public when that field changes.
 rhs='p.'+path if name in ['anchor','nullifier','recipient','change','next_root'] else {'index':'0#u64','frontier':'empty_frontier','next_frontier':'empty_frontier'}[name]
 out.append(f'theorem digest_field_{name} (p : reference_terminal.SemanticPublic) :\n    (valid_public p).{path} = {rhs} := rfl\n#print axioms digest_field_{name}\n')
out.append('''theorem digest_field_opened (o : aspis_statement.state_only_poseidon.StateOnlyPoseidonOpenings) :
    o.z = o.z := rfl
#print axioms digest_field_opened
end PV_B3P_Success227
''')
files={'PV_B3P_DigestFields227':'\n'.join(out)}
input_names=[]
for i,ch in enumerate(chunks):
 name=f'digest_stage_{i:02}'
 if i==0: inp=None
 else:
  inp='digests'+str(i) if i<=4 else 'digests'+str(i)
 # For stage1 input digests1; stage2 digests2; ... stage24 digests24.
 if i:assert re.search(r'\b'+inp+r'\b',ch),(i,inp)
 # The final top-level digest assignment is the stage's output, convert it into return.
 if i<24:
  var='digests'+str(i+1)
  pat='  let '+var+' ←\n'
  if pat in ch:
   before,after=ch.split(pat,1);ch=before+'\n'.join(l[2:] for l in after.splitlines())
  else:
   pat='  let '+var+' ←'
   assert pat in ch,(i,ch)
   ch=ch.replace(pat,' ')
  # Dedent the former RHS from4-space block to2 spaces if multiline.
  ls=ch.splitlines();start=next(j for j,l in enumerate(ls)if not l.startswith('  let ') and (j==0 or ls[j-1].startswith('  let ') or ls[j-1].startswith('    '))) if False else 0
  # Removing let leaves multiline RHS indented4. Lean accepts this after preceding do statements.
 if i:ch=re.sub(r'\b'+inp+r'\b','output',ch)
 definition=f'def {name} {params}'+(' (output : Digest8Q)'if i else '')+' : Result Digest8Q := do\n'+ch+'\n'
 # Stage-level successes use existing named callee laws; branch-specific totality below.
 proof=['  unfold '+name]
 if i in [0,1,3]:
  proof += ['  apply lift_total','  apply lift_total','  apply bind','  · apply row_total','    apply row_address_bound <;> scalar_tac','  intro selector','  apply total_reference_terminal_add_digest_binding <;> scalar_tac']
 elif i==2:
  proof += ['  cases public1.recipient with','  | none => exact ok _','  | some expected =>','    apply lift_total','    apply lift_total','    apply bind','    · apply row_total','      apply row_address_bound <;> scalar_tac','    intro selector','    apply total_reference_terminal_add_digest_binding <;> scalar_tac']
 elif i<24:
  proof += ['  apply lift_total','  apply lift_total','  apply lift_total','  split','  · apply lift_total','    apply bind','    · apply row_total','      apply row_mul_bound','      apply wrap_add_bound; scalar_tac','    intro selector','    apply bind','    · apply empty_root_total; scalar_tac','    intro expected','    apply total_reference_terminal_add_digest_binding','    unfold aspis_statement.poseidon2.RATE','    scalar_tac','  · apply lift_total','    apply lift_total','    apply bind','    · apply row_total','      apply row_address_bound','      · apply wrap_add_bound; scalar_tac','      · scalar_tac','    intro selector','    apply bind','    · apply digest_total; scalar_tac','    intro expected','    apply total_reference_terminal_add_digest_binding <;> scalar_tac']
 else:
  proof += ['  apply lift_total','  apply lift_total','  apply bind','  · apply row_total','    apply row_address_bound <;> scalar_tac','  intro selector','  apply bind','  · apply total_reference_terminal_add_digest_binding <;> scalar_tac','  intro digests25','  apply bind','  · exact carry_total _','  intro carry','  split','  · apply lift_total','    apply lift_total','    apply lift_total','    apply bind','    · apply row_total','      apply row_address_bound','      · apply wrap_add_bound; scalar_tac','      · scalar_tac','    intro selector','    apply bind','    · apply index; scalar_tac','    intro expected','    apply total_reference_terminal_add_digest_binding <;> scalar_tac','  · exact ok _']
 mod=f'PV_B3P_DigestStage{i:02}227'
 text='import PV_B3P_DigestFields227\n'+header.replace('abbrev Digest8Q := Array aspis_core.field.QM31 8#usize\n','')+definition+f'\ntheorem {name}_success {params}'+(' (output : Digest8Q)'if i else '')+f' :\n    Success ({name} public1 openings selectors'+(' output'if i else '')+') := by\n'+'\n'.join(proof)+f'\n\n#print axioms {name}_success\nend PV_B3P_Success227\n'
 files[mod]=text
# Compose opaque stages, then check the syntax-factoring equality separately.
imports=''.join('import PV_B3P_DigestStage%02227\n'%i if False else f'import PV_B3P_DigestStage{i:02}227\n'for i in range(25))
stages='\n'.join(f'  let d{i} ← digest_stage_{i:02} public1 openings selectors'+(f' d{i-1}'if i else '')for i in range(24))+'\n  digest_stage_24 public1 openings selectors d23\n'
seq=f'def digest_sequence {params} : Result Digest8Q := do\n'+stages
factor=f'theorem digest_factor {params} :\n    reference_terminal.public_digest_lanes public1 openings selectors =\n      digest_sequence public1 openings selectors := by\n  rfl\n#print axioms digest_factor\n'
proof='  unfold digest_sequence\n'+''.join(f'  apply bind\n  · exact digest_stage_{i:02}_success public1 openings selectors'+(f' d{i-1}'if i else '')+f'\n  intro d{i}\n'for i in range(24))+'  exact digest_stage_24_success public1 openings selectors d23\n'
files['PV_B3P_DigestSequence227']=imports+header.replace('abbrev Digest8Q := Array aspis_core.field.QM31 8#usize\n','')+seq+factor+f'theorem digest_sequence_success {params} :\n    Success (digest_sequence public1 openings selectors) := by\n'+proof+'\n#print axioms digest_sequence_success\n'+f'theorem public_digest_success8 {params} :\n    Success (reference_terminal.public_digest_lanes public1 openings selectors) := by\n  rw [digest_factor]\n  exact digest_sequence_success public1 openings selectors\n#print axioms public_digest_success8\nend PV_B3P_Success227\n'
for m,t in files.items():
 p=L/(m+'.lean')
 if '--check'in sys.argv:assert p.read_text()==t,m
 else:p.write_text(t)
print(json.dumps(dict(modules=list(files),original_body_sha256=hashlib.sha256(body.encode()).hexdigest())))
