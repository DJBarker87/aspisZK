"""Factor required generic declarations out of historical fixture closures."""
from pathlib import Path
import re,json,hashlib,sys
R=Path(__file__).resolve().parents[2];P=Path(__file__).resolve().parent
core=['JGk_TX2_ParentWrite','JGm_TX2_BinarySelect','JGm_TX2_Scalar','JGm_TX2_ReadCell','JGm_TX2_Supplied','JGm_TX2_ExternalRun','JGm_TX2_RowControl','JGk_TX2_ZeroWindows']
padding=['JGm_TX2_PaddingScan','JGu_Supplied','JGu_Padding0','JGu_Padding1','JGu_Padding2','JGu_PaddingScan']
partial=['JGc_TX2_RealLeaves','JGc_TX2_LeafHelpers','JGh_TX2_NodeViews','JGk_TX2_ScratchIndices']
ns={x:'JGy_G_'+x for x in core+padding+partial}
pat=re.compile(r'\b('+'|'.join(map(re.escape,ns))+r')\b')
rename=lambda s:pat.sub(lambda m:ns[m[0]],s)
body=lambda x:'\n'.join(l for l in (R/'lean'/f'{x}.lean').read_text().splitlines() if not l.startswith('import '))+'\n'
def partial_body(module,start,stop):
 s=(R/'lean'/f'{module}.lean').read_text();s=s[s.index(start):];s=s[:s.index(stop)+len(stop)]
 return f'set_option autoImplicit false\nnoncomputable section\nnamespace AspisR1.{module}\nopen Aeneas Aeneas.Std Result\n'+s+'\nend AspisR1.'+module+'\nend\n'
a=[]
s=(R/'lean/JGc_TX2_RealLeaves.lean').read_text();s=s[s.index('def dictionary'):s.index('def value')]
a.append('set_option autoImplicit false\nnamespace AspisR1.JGc_TX2_RealLeaves\n'+s+'end AspisR1.JGc_TX2_RealLeaves\n')
a.append(body('JGc_TX2_LeafHelpers'))
a.append(partial_body('JGh_TX2_NodeViews','@[irreducible] def readCell','#print axioms read_selected'))
a.append(partial_body('JGk_TX2_ScratchIndices','theorem snoc_set','#print axioms snoc_set'))
a.extend(body(x) for x in core)
imports=['JGm_TX2_View','Port4B_Install','Port4B_VerifyInstall','Port3_NativeBatchBody','MultiproofConePhysicalAddress','MultiproofConePhysicalDigest','MultiproofConeRead32','MultiproofConeSlices','JFp_SHADigest','F3U_Oracle','OracleDecisionMultiTree','JFq_Range']
texts={'JGy_LightCore':''.join('import '+x+'\n' for x in imports)+rename('\n'.join(a)), 'JGy_LightPadding':'import JGy_LightCore\nimport JGm_TX2_AnyFalse\nimport JGp_Slot0\nimport JGp_Slot1\nimport JGp_Slot2\n'+rename('\n'.join(body(x) for x in padding))}
for mod,text in texts.items():
 f=R/'lean'/f'{mod}.lean'
 if '--check' in sys.argv:assert f.read_text()==text
 else:f.write_text(text)
manifest=dict(namespaces=ns,module_map={**{x:'JGy_LightCore' for x in core+partial},**{x:'JGy_LightPadding' for x in padding}},removed_unused_imports=['JGk_TX2_SiblingLaws'],removed_unused_irreducible_attributes=['JGh_TX2_NodeViews.nodes0','JGh_TX2_NodeViews.nodes1','JGh_TX2_NodeViews.nodes2'],sources={x:hashlib.sha256((R/'lean'/f'{x}.lean').read_bytes()).hexdigest() for x in core+padding+partial},partial_exports={'JGc_TX2_RealLeaves':['dictionary'],'JGc_TX2_LeafHelpers':['four'],'JGh_TX2_NodeViews':['readCell','read_selected'],'JGk_TX2_ScratchIndices':['snoc_set']},new_source_hashes={m:hashlib.sha256(s.encode()).hexdigest() for m,s in texts.items()})
(P/'JGy_LIGHT.json').write_text(json.dumps(manifest,indent=2)+'\n')
print('Factored',len(core)+len(padding)+len(partial),'generic source modules into two files; unused fixture declarations excluded')
