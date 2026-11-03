from pathlib import Path
import subprocess,json,re,hashlib
E=Path(__file__).resolve().parent;R=E.parent.parent
modules=['FIo_FieldBridge','FIo_ReduceBridge','FIo_M31Bridge','FIo_M31SubBridge','FIo_M31MulBridge','LPf_CoreReduction','LPf_BaseMultiply','LPi_Total','LPi_NatBase','LPi_CMProduct','LPi_FieldValues','LPi_TowerValues','LPi_MixedValues','NEB_FieldDomains','NEB_CMCalls','NEB_QMCalls','NEB_ByRCalls','NBG_WideCarriers','NEB_WideCalls','NEB_AdditiveCalls','NEB_CMCarrier','NEB_NativeFieldScalars']
rename={n:'NEI_'+n for n in modules}
rename['LPf_ReductionWord']='_root_.NEI_ReductionWord'
rename['NEB_MulReducerCall']='NEI_UnusedMulReducerCall'
head='import NEI_FieldWide\nimport NEI_LineDomains\nimport NEI_ReductionWord\nimport FIo_ReduceBounds\nimport FIo_ScalarBridge\nnoncomputable section\n'
parts=[];records=[]
for module in modules:
 path=('evidence/slice-q-compose-20261029/' if module.startswith('NEB_') else 'lean/')+module+'.lean'
 raw=subprocess.check_output(['git','show','HEAD:'+path],cwd=R).decode()
 kept=raw
 if module=='NBG_WideCarriers':
  lo=raw.index('theorem remainder ');hi=lo
  # Keep exactly this declaration, ending before the following declaration.
  end=raw.index('\ntheorem canonical_qm31',lo)
  kept='namespace NBG_WideCarriers\nopen Aeneas Aeneas.Std Result\n'+raw[lo:end]+'\n#print axioms remainder\nend NBG_WideCarriers\n'
 if module=='NEB_WideCalls':
  lo=kept.index('theorem mixed ');hi=kept.index('theorem scale ',lo);kept=kept[:lo]+kept[hi:];kept=kept.replace('#print axioms mixed\n','')
 if module=='NEB_NativeFieldScalars':
  lo=kept.index('theorem m31_checked_product ');hi=kept.index('theorem sum_checked ',lo);kept=kept[:lo]+kept[hi:];kept=kept.replace('#print axioms m31_checked_product\n','')
 without_imports='\n'.join(l for l in kept.splitlines() if not l.startswith('import '))+'\n'
 transformed=re.sub(r'\b('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')\b',lambda m:rename[m[0]],without_imports)
 parts.append('-- Unchanged retained declarations from '+path+'\n'+transformed)
 records.append(dict(module=module,original=path,revision=subprocess.check_output(['git','rev-parse','HEAD'],cwd=R,text=True).strip(),sha256=hashlib.sha256(raw.encode()).hexdigest(),text=raw,retained_before_renaming=without_imports,transformed_sha256=hashlib.sha256(transformed.encode()).hexdigest()))
(E/'NEI_ReplayFieldArithmetic.lean').write_text(head+'\n'.join(parts)+'\nend\n')
(E/'NEI_PROFILE_REPLAY_INPUTS.json').write_text(json.dumps(dict(imports=head,renames=rename,entries=records,qualification='Private replay of retained mathematical declarations only; no historical native credit'),indent=2)+'\n')
p=E/'NEI_ProfileDomain.lean';s=p.read_text();s='\n'.join(l for l in s.splitlines() if not l.startswith('import '))+'\n';s=re.sub(r'\b('+'|'.join(map(re.escape,sorted(rename,key=len,reverse=True)))+r')\b',lambda m:rename[m[0]],s);p.write_text('import '+('NEI_ProfilePair' if 'NEI_ProfilePair.wide_pair' in s else 'NEI_ReplayFieldArithmetic')+'\n'+s)
