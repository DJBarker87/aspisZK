from pathlib import Path
import re
src=Path('evidence/port17release-20261024/dependency-source/S1SemanticBudgetV1.lean').read_text()
previous='GExp_AssociationTactic'
prior=[]
for match in re.finditer(r'theorem (\w+)_bounded\s+(.*?)(?=\nattribute \[local irreducible\])',src,re.S):
    name,body=match.groups()
    sig=body.split(' := by')[0]
    sig=re.sub(r': bounded \d+ \(',r'(hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)\n    (law : ∀ h parts, D.digest h parts = hashv parts) :\n    AspisR1.SdkD_PrepareLower.Associated hashv (',sig)
    children=re.findall(r'budget_then_for \d+ (\w+)',body)
    proof=f'  unfold {name}\n  repeat\' first\n    | (solve | apply pure_associated)\n    | (solve | apply lift_associated)\n'
    for child in children:
        proof+=f'    | (solve | exact {child}_associated _ _' + ')\n' if False else ''
        proof+=f'    | (solve | apply {child}_associated; exact law)\n'
        proof+=f'    | (association_then_for {child}\n       <;> first | (solve | apply {child}_associated; exact law) | intro x)\n'
    proof+='    | (apply lift_bind_associated; intro x)\n    | (association_then\n       <;> first | (solve | apply digest_associated; exact law _ _) | intro x)\n    | split\n'
    module='GExp_'+name[0].upper()+name[1:]+'Association'
    text=f'import {previous}\nset_option autoImplicit false\nnamespace AspisR1PublicPreparation.S1SemanticCode\nopen Aeneas Aeneas.Std Result\nopen PreparedHashCode\nopen AspisR1.GExp_Association\nattribute [local irreducible] PreparedHashCode.effects'+(' '+' '.join(prior) if prior else '')+'\n\n'
    text+=f'theorem {name}_associated '+sig+' := by\n'+proof+f'\n#print axioms {name}_associated\nend AspisR1PublicPreparation.S1SemanticCode\n'
    Path('lean/'+module+'.lean').write_text(text)
    previous=module;prior.append(name)
src=Path('evidence/port17release-20261024/dependency-source/S1PreparedBudgetV1.lean').read_text()
prior=[]
for match in re.finditer(r'theorem (\w+)_bounded\s+(.*?)(?=\nattribute \[local irreducible\])',src,re.S):
    name,body=match.groups(); sig=body.split(' := by')[0]
    sig=re.sub(r': bounded \d+ \(',r'(hashv : AspisR1.SdkC_Source.Parts → Result AspisR1.SdkC_Source.Digest)\n    (law : ∀ h parts, D.digest h parts = hashv parts) :\n    AspisR1.SdkD_PrepareLower.Associated hashv (',sig)
    fn=re.search(r'  unfold (\S+)',body)[1]; children=re.findall(r'budget_then_for \d+ (\S+)',body)
    childproof=re.findall(r'\(solve \| apply (\w+)_bounded\)',body)
    pairs=list(zip(children,dict.fromkeys(childproof)))
    proof=f'  unfold {fn}'+(' preparationEffects' if name=='preparation' else '')+'\n  repeat\' first\n    | (solve | apply pure_associated)\n    | (solve | apply lift_associated)\n'
    for child,lemma in pairs:
        proof+=f'    | (solve | apply {lemma}_associated; exact law)\n'
        proof+=f'    | (association_then_for {child}\n       <;> first | (solve | apply {lemma}_associated; exact law) | intro x)\n'
    proof+='    | (apply lift_bind_associated; intro x)\n    | (association_then\n       <;> first | (solve | apply digest_associated; exact law _ _) | intro x)\n    | split\n'
    module='GExp_Prepared'+name[0].upper()+name[1:]+'Association'
    text=f'import {previous}\nset_option autoImplicit false\nnamespace AspisR1PublicPreparation.PreparedBudget\nopen Aeneas Aeneas.Std Result\nopen PreparedHashCode\nopen AspisR1.GExp_Association\nattribute [local irreducible] PreparedHashCode.effects'+(' '+' '.join(prior) if prior else '')+'\n\n'
    text+=f'theorem {name}_associated '+sig+' := by\n'+proof+f'\n#print axioms {name}_associated\nend AspisR1PublicPreparation.PreparedBudget\n'
    Path('lean/'+module+'.lean').write_text(text);previous=module;prior.append(fn)
