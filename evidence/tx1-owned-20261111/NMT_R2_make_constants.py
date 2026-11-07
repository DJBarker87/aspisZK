from pathlib import Path
p=Path(__file__).resolve().parent
base='AdapterRw.aspis_r1_cost_probe.'
def ar(op,a,b,c):
 f={'a':'NMT_R2_SmallAdd.checked_add','m':'NMT_R2_ScalarArithmetic.mul'}[op]
 proof = f'(by change {a} * {b} = {c}; rw [Nat.mul_comm]; rfl)' if op=='m' and b>a else 'rfl'
 return f'({f} {a}#usize {b}#usize {c}#usize {proof})'
def th(name,path,val,defs,deps=(),edges=(),sub=None):
 lines=[f'theorem {name} : {base+path} = .ok {val}#usize := by',f' unfold {base+path}']
 if defs:lines.append(' unfold '+' '.join(base+x for x in defs))
 rules=list(deps)+[ar(*e) for e in edges]+['bind_tc_ok']
 if sub:
  a,b,c=sub;rules.insert(-1,f'(NMT_R2_ScalarArithmetic.sub {a}#usize {b}#usize {c}#usize (by decide) rfl)')
 lines+=[' simp only ['+',\n  '.join(rules)+']',f'#print axioms {name}','']
 return '\n'.join(lines)
def write(module,imports,contents):
 (p/(module+'.lean')).write_text('\n'.join('import '+i for i in imports)+'\nset_option autoImplicit false\nnamespace '+module+'\nopen Aeneas Aeneas.Std\n'+contents+'\nend '+module+'\n')
a=th('nodes','compact.MAX_NODES',914,[],edges=[('a',146,172,318),('m',2,318,636),('a',128,150,278),('a',636,278,914)])
a+=th('semantic','verifier.SEMANTIC_BYTES',13831,[],edges=[('m',29,32,928),('a',12903,928,13831)])
a+=th('values','compact.SEMANTIC_COMPACT_VALUES',426,[],edges=[('m',10,28,280),('a',1,280,281),('a',87,29,116),('a',281,116,397),('a',397,29,426)])
write('NMT_R2_ConstantsA',['NMT_R2_SmallAdd','NMT_R2_ScalarArithmetic'],a)
b=th('semantic','compact.COMPACT_SEMANTIC',7015,['compact.LOGICAL_SEMANTIC'],deps=['NMT_R2_ConstantsA.semantic','NMT_R2_ConstantsA.values'],edges=[('m',16,426,6816)],sub=(13831,6816,7015))
b+=th('y1','compact.OFF_Y1',7031,['compact.OFF_SEMANTIC','compact.HEADER'],deps=['semantic'],edges=[('a',16,7015,7031)])
b+=th('inactive','compact.OFF_INACTIVE',7495,['compact.COMPACT_Y1'],deps=['y1'],edges=[('m',29,16,464),('a',7031,464,7495)])
b+=th('round0','compact.OFF_ROUND0',7527,[],deps=['inactive'],edges=[('a',7495,32,7527)])
b+=th('folded','compact.OFF_FOLDED_ROOT',7751,[],deps=['round0'],edges=[('a',7527,224,7751)])
b+=th('round1','compact.OFF_ROUND1',7783,[],deps=['folded'],edges=[('a',7751,32,7783)])
b+=th('final','compact.OFF_FINAL',8007,[],deps=['round1'],edges=[('a',7783,224,8007)])
write('NMT_R2_ConstantsB',['NMT_R2_ConstantsA'],b)
c=th('opening','compact.OPENING',832,[],edges=[('a',480,128,608),('a',608,32,640),('a',640,32,672),('a',672,128,800),('a',800,32,832)])
c+=th('openings','compact.OFF_OPENINGS',10055,['compact.FINAL_LEN'],deps=['NMT_R2_ConstantsB.final'],edges=[('m',64,32,2048),('a',8007,2048,10055)])
c+=th('fixed','compact.FIXED',28359,['compact.OFF_NODES','compact.QUERIES'],deps=['opening','openings'],edges=[('m',22,832,18304),('a',10055,18304,28359)])
c+=th('proof','verifier.PROOF_BYTES',57607,['compact.PROOF_BYTES','compact.MAX_PROOF'],deps=['NMT_R2_ConstantsA.nodes','fixed'],edges=[('m',32,914,29248),('a',28359,29248,57607)])
write('NMT_R2_ConstantsC',['NMT_R2_ConstantsB'],c)
