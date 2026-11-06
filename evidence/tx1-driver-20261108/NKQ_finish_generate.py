from pathlib import Path
import textwrap,re,hashlib,json
E=Path(__file__).resolve().parent
src=(E.parent/'claims2-20261108/NKA_generated/NKA_FinishStages.lean').read_text()
p=E/'NKQ_generated/NKQ_FinishStages.lean';old=p.read_text()
s=src[src.index('  let cf ←'):src.index('\n\n\n/-- Whole')]
head=old[:old.index('/-- Literal')]
args=old[old.index('def afterTerminal')+len('def afterTerminal'):old.index('\n (val1 : Claims)')]
roundArgs=old[old.index('def afterRounds')+len('def afterRounds'):old.index('\n (r : NKA_FinishStages.RoundOut H)')]
proof=old[old.index('\ntheorem factor'):]
t=s.index('      let cf2 ←');te=re.search(r'^    \| core.ops.control_flow.ControlFlow.Break residual =>',s[t:],re.M).start()+t
term=textwrap.dedent(s[t:te])
s1=s[:t]+'      afterTerminal reservation aspis_coreDigest32Inst public1 prefix1 challenges running alpha transcript1 val1 r3\n'+s[te:]
c=s1.index('    let cf1 ←');ce=re.search(r'^  \| core.ops.control_flow.ControlFlow.Break residual =>',s1[c:],re.M).start()+c
claims=textwrap.dedent(s1[c:ce]);s2=s1[:c]+'    afterClaims reservation aspis_coreDigest32Inst public1 prefix1 challenges running alpha transcript1 r1\n'+s1[ce:]
termDef='/-- Literal source suffix around OPEN terminal256, not native credit. -/\ndef afterTerminal'+args+'\n (val1 : Claims) (r3 : core.result.Result Q r1_wire.Error) : Result (Out H) := do\n'+textwrap.indent(term,'  ')
claimsDef='\n\ndef afterClaims'+args+'\n (r1 : core.result.Result Claims r1_wire.Error) : Result (Out H) := do\n'+textwrap.indent(claims,'  ')
roundDef='\n\ndef afterRounds'+roundArgs+'\n (r : NKA_FinishStages.RoundOut H) : Result (Out H) := do\n'+s2+'\n'
p.write_text(head+termDef+claimsDef+roundDef+proof)
(E/'NKQ_FINISH_GENERATION.json').write_text(json.dumps(dict(input='evidence/claims2-20261108/NKA_generated/NKA_FinishStages.lean',input_sha256=hashlib.sha256(src.encode()).hexdigest(),output_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),repair='Anchor branch indentation so every nested error branch is retained'),indent=2))
