from pathlib import Path
import json,re
E=Path(__file__).resolve().parent
raw=(E/'NNG_SourceSuffixes.lean').read_text()
s=raw.replace('namespace AspisR1.NNG_SourceSuffixes','namespace AspisR1.NNG_TreeSuffixes').replace('end AspisR1.NNG_SourceSuffixes','end AspisR1.NNG_TreeSuffixes')
s=s.replace('import NNG_EmittedContext','import NNG_EmittedContext\nimport NNG_TraceAlgebra')
s=s.replace('NNG_verify_finish NNG_Emitted','NNG_verify_finish NNG_Emitted NMT_CallTree')
s=s.replace(': Result (Output H) := do',': Code (Output H) := do')
s=re.sub(r'\bok \(', 'pure (',s)
s=re.sub(r'(?m)^(\s*)core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual',r'\1monadLift <| core.result.Result.Insts.CoreOpsTryTraitFromResidualResultInfallible.from_residual',s)
replacements=[
 (r'c\.c10 aspis_coredigestDigest32Inst prefix1 transcript','"rounds"','(prefix1,transcript)','c.c10 aspis_coredigestDigest32Inst prefix1 transcript'),
 (r'c\.c8 prefix1','"claims"','prefix1','c.c8 prefix1'),
 (r'c\.c7\s+public1 val1 alpha challenges','"terminal"','(public1,val1,alpha,challenges)','c.c7 public1 val1 alpha challenges'),
 (r'c\.c6 a a1 q\s+alpha','"mask"','(a,a1,q,alpha)','c.c6 a a1 q alpha'),
 (r'c\.c11 prefix1 25#u8','"record25"','(prefix1,25#u8)','c.c11 prefix1 25#u8'),
 (r'c\.c11 prefix1 26#u8','"record26"','(prefix1,26#u8)','c.c11 prefix1 26#u8'),
 (r'c\.c15 29#usize vr 87#usize','"extra"','(vr,87#usize)','c.c15 29#usize vr 87#usize'),
 (r'c\.c15 29#usize vr2 0#usize','"beforeZ1"','(vr2,0#usize)','c.c15 29#usize vr2 0#usize'),
 (r'c\.c5 challenges.eta val2','"multiply"','(challenges.eta,val2)','c.c5 challenges.eta val2'),
 (r'c\.c4 mask q1','"addMask"','(mask,q1)','c.c4 mask q1'),
 (r'c\.c4 q2 q3','"addExtra"','(q2,q3)','c.c4 q2 q3'),
 (r'c\.c14\s+aspis_coredigestDigest32Inst transcript1','"state"','transcript1','c.c14 aspis_coredigestDigest32Inst transcript1'),
 (r'c\.c13\s+aspis_coredigestDigest32Inst transcript1 vr1','"circle0"','(transcript1,vr1)','c.c13 aspis_coredigestDigest32Inst transcript1 vr1'),
 (r'c\.c13\s+aspis_coredigestDigest32Inst transcript2 vr3','"circle1"','(transcript2,vr3)','c.c13 aspis_coredigestDigest32Inst transcript2 vr3'),
 (r'c\.c12 prefix1 2#u8','"payload2"','(prefix1,2#u8)','c.c12 prefix1 2#u8')]
for i in [2,3,4,5]: replacements.append((fr'c\.c9 obs {i}#u8',f'"mark{i}"',f'(obs,{i}#u8)',f'c.c9 obs {i}#u8'))
for pat,site,arg,call in replacements:
 s,n=re.subn(pat,lambda _:f'invoke {site} {arg} ({call})',s)
 assert n==1,(pat,n)
(E/'NNG_TreeSuffixes.lean').write_text(s)
points=json.load(open(E/'NNG_SOURCE_OCCURRENCES.json'))
previous=None;proofs=[]
for p in reversed(points):
 name=p['name'];module='NNG_Erase_'+name
 dependencies='import NNG_TreeSuffixes\nimport NNG_SourceSuffixes\n'+('import NNG_TraceCongruence\n' if name not in ['a3','r11','r10'] else '')+('import '+previous+'\n' if previous else '')
 # Only previous suffix theorem names are supplied: source-order fission
 # ensures all dependencies precede this proof in reverse lexical order.
 lemmas=', '.join('erase_'+x for x in proofs)
 text=dependencies+'''set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_TreeErasure
open Aeneas Aeneas.Std Result NNG_verify_finish NNG_Emitted NMT_CallTree NNG_TraceAlgebra
'''
 args=p['args'];app=' '+p['app'] if p['app'] else ''
 text+=f'''theorem erase_{name} {{H W : Type}} (c : Calls) (s : Parent H W){args} :
    erase (NNG_TreeSuffixes.f_{name} c s{app}) = NNG_SourceSuffixes.f_{name} c s{app} := by
  simp only [NNG_TreeSuffixes.f_{name}, NNG_SourceSuffixes.f_{name},
    erase_bindM, NMT_CallTree.erase_invoke, erase_liftM, NNG_TraceAlgebra.erase_lift,
    erase_pureM, erase_control, erase_if{', '+lemmas if lemmas else ''}] <;> rfl
#print axioms erase_{name}
end AspisR1.NNG_TreeErasure
'''

 if name=='r10':
  start=text.index('  simp only');end=text.index('#print',start)
  text=text[:start]+'''  unfold NNG_TreeSuffixes.f_r10 NNG_SourceSuffixes.f_r10
  rw [erase_bindM, NMT_CallTree.erase_invoke]
  apply result_congr
  intro reply
  rw [erase_bindM, erase_liftM]
  apply result_congr
  intro cf
  cases cf with
  | Continue val7 => exact erase_r11 c s alpha val1 val3 state_before_z0 val4 val5 transcript3 val6 val7
  | Break residual => exact NNG_TraceAlgebra.erase_lift _
'''+text[end:]
 (E/(module+'.lean')).write_text(text)
 previous=module;proofs.append(name)
(E/'NNG_TREE_ERASURE_ORDER.json').write_text(json.dumps(['NNG_SourceSuffixes','NNG_TreeSuffixes']+['NNG_Erase_'+p['name'] for p in reversed(points)],indent=2)+'\n')
print(len(points),'suffixes')
