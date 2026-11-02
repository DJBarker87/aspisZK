"""Emit small caller compositions using named complete-Result helper equalities."""
from pathlib import Path
import re,json,hashlib,sys
D=Path('evidence/pv-b3p6-20261028');O=D/'lean';rows=[]
def body(file,name):
 p=O/file;s=p.read_text();start=s.index('def '+name);m=re.search(r'\n(?:theorem|def |/--|end )',s[start+4:]);end=start+4+m.start()if m else len(s)
 # End immediately before the next declaration/doc; generated source has no nested top-level def.
 return s[start:end].strip(),p
semantic,p=body('PV_B3P_E227_46.lean','reference_terminal.semantic_packed')
semantic=semantic.replace('def reference_terminal.semantic_packed','def semantic_callees557',1)
subs={'reference_terminal.add_schedule_lanes':'local_bodies557.body4','reference_terminal.add_path_lanes':'local_bodies557.body2','reference_terminal.add_value_lanes':'local_bodies557.body5','reference_terminal.public_digest_lanes':'local_bodies557.body11','reference_terminal.add_preweighted':'local_bodies557.body3'}
for a,b in subs.items():assert a in semantic;semantic=semantic.replace(a,b)
rows.append(dict(target='semantic_callees557',source=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),substitutions=subs))
header='''import PV_B3P_LocalClosure557227
namespace PV_B3P_Closure557227
open Aeneas Aeneas.Std PV_B3P_227 PV_B3P_Success227 Result ControlFlow Error
set_option autoImplicit false
noncomputable section
attribute [local irreducible] local_bodies557
/-- Same caller control/dataflow with the fixed bound local callees substituted.
Remaining unchanged helpers and std/source coverage are separate obligations. -/
'''
s=header+semantic+'''

theorem semantic_callees_reference557 :
    semantic_callees557 = reference_terminal.semantic_packed := by
  unfold semantic_callees557 reference_terminal.semantic_packed
  rw [local_links557.link4,local_links557.link2,local_links557.link5,
    local_links557.link11,local_links557.link3]

#print axioms semantic_callees_reference557
end
end PV_B3P_Closure557227
'''
(O/'PV_B3P_SemanticCallees557227.lean').write_text(s)
composition,p=body('PV_B3P_CompositionSource554227.lean','composition_source554')
composition=composition.replace('def composition_source554','def composition_callees557',1)
subs={'reference_terminal.validate_transition':'local_bodies557.body16','reference_terminal.poseidon_selectors':'local_bodies557.body10','reference_poseidon.evaluate_state_only_poseidon_oracle_projected':'local_bodies557.body23','reference_terminal.semantic_packed':'semantic_callees557'}
for a,b in subs.items():assert a in composition;composition=composition.replace(a,b)
rows.append(dict(target='composition_callees557',source=str(p),source_sha256=hashlib.sha256(p.read_bytes()).hexdigest(),substitutions=subs))
s=header.replace('import PV_B3P_LocalClosure557227','import PV_B3P_SemanticCallees557227\nimport PV_B3P_HornerLoopBinding8227')+composition+'''

theorem composition_callees_reference557 :
    composition_callees557 = reference_terminal.composition_parts := by
  have restored : composition_callees557 = PV_B3P_Association554227.composition_source554 := by
    unfold composition_callees557 PV_B3P_Association554227.composition_source554
    rw [local_links557.link16,local_links557.link10,local_links557.link23,
      semantic_callees_reference557]
  exact Eq.trans restored PV_B3P_Association554227.composition_source_link554

#print axioms composition_callees_reference557
end
end PV_B3P_Closure557227
'''
(O/'PV_B3P_CompositionCallees557227.lean').write_text(s)
manifest=D/'resume18/CALLEE-SUBSTITUTIONS-D557.json';manifest.write_text(json.dumps(rows,indent=2)+'\n')
print('generated two bounded caller compositions')
