from pathlib import Path
import re
R=Path(__file__).resolve().parents[2]
# Proof-source transformation only: preserve actual validator/encoder observations.
chain=['SAP_Claims','SAP_Op3','SAP_Tx2','SAP_Success','SAP_Batches','SAP_Union','SAP_SdkUnion','SAP_SdkAccepted','SAP_CPhy','SAP_Physical','SAP_FinishEffects','SAP_NativePair']
mapping={'SAP_D189':'P2P_D189'}
for name in chain:
 new='P2P_'+name.removeprefix('SAP_')
 s=(R/'lean'/f'{name}.lean').read_text()
 preds=[old for old in mapping if old+'.' in s]
 s=''.join('import '+mapping[old]+'\n' for old in preds)+s
 s=s.replace('AspisR1.'+name,'AspisR1.'+new)
 for old in preds:s=s.replace(old+'.',mapping[old]+'.')
 # Preserve old imports; only new theorem calls and namespace differ.
 m=re.search(r'SourceCuts (.*?) e1.first \(e2.second secondSizes\) saved f s ∧',s,re.S)
 assert m,(name,'no initial cuts')
 ops=m.group(1)
 # First result cut only. Later selected-cut assertions stay verbatim.
 s=s[:m.end()]+f'\n      P2P_Origin.Fact {ops} program (e2.second secondSizes) data2 slot s ∧'+s[m.end():]
 # Every result producer/destructor carrying these cuts must pass origin.
 s=re.sub(r'(⟨f,\s*s,\s*outer,\s*pre,\s*middle,\s*fs,\s*ss,\s*cuts,)',r'\1origin,',s)
 # D189 places origin before cuts; normalize its Claims consumer explicitly.
 if name=='SAP_Claims':
  s=s.replace('fs, ss, cuts,origin,','fs, ss, origin, cuts,',1)
  # The result tuple is normalized to after-cuts origin by transformation above.
 # Remove verbose proof term printing. All new top theorems keep #print axioms.
 s=re.sub(r'^#print (?!axioms).*\n','',s,flags=re.M)
 (R/'lean'/f'{new}.lean').write_text(s)
 mapping[name]=new
(R/'evidence/p2prime-20261026/P2P_provenance_mapping.json').write_text(__import__('json').dumps(mapping,indent=2)+'\n')
