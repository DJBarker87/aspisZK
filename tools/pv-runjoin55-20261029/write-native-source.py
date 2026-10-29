from pathlib import Path
R=Path(__file__).resolve().parents[2];L=R/'docs/research/v8-r0-zk-20261009/lean/R1Z'
p=L/'PV_RunJoin_NativeControlSource55.lean';s=p.read_text();a=s.index(' := by\n');z=s.index('\n#print',a)
proof=(L/'PV_RunJoin_NativeAuditRel55.lean').read_text();proof=proof[proof.index('  apply PV_RunJoin_ResultRelation55.same_bind'):proof.index('\n#print')]
proof=proof.replace('PV_RunJoin_ResultRelation55.same_bind','PV_RunJoin_ResultBindEq55.complete').replace('exact PV_RunJoin_NativeResult55.error R _ _','rfl')
last=proof.splitlines()[-1];indent=last[:len(last)-len(last.lstrip())];proof='\n'.join(proof.splitlines()[:-1])+'\n';lines=[]
def emit(x):lines.append(indent+x)
def bind(n):emit('apply PV_RunJoin_ResultBindEq55.complete');emit('intro '+n)
def case(n,v):
 global indent
 emit('cases '+n+' with');emit('| Err e => rfl');emit('| Ok '+v+' =>');indent+='  ';emit('simp only [core.result.Result.Insts.CoreOpsTry.branch,bind_tc_ok]')
bind('tag1');bind('saltResult1');case('saltResult1','salts1');bind('tag2');bind('saltResult2');case('saltResult2','salts2');bind('domainResult');bind('mappedDomain');case('mappedDomain','domain');bind('zero');bind('messages');bind('builtPair');emit('dsimp only [Aeneas.Std.uncurry]');bind('builtStatus');case('builtStatus','sem');bind('column');bind('total');bind('zeroQ');bind('balanced');emit('cases balanced with');emit('| false => rfl');emit('| true =>');indent+='  ';emit('rw [PV_RunJoin_NativePhaseSource55.complete]')
# rw closes syntactic equality automatically if possible; remaining reflexivity is guarded.
emit('all_goals rfl')
proof+= '\n'.join(lines)
s=s[:a]+''' := by
  unfold prover.prove_masked_with_attempt PV_RunJoin_NativeControl55.run
'''+proof+'\n'+s[z:];p.write_text(s)
