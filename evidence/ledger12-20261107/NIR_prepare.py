from pathlib import Path
import json,re,difflib,lzma,hashlib,subprocess
E=Path(__file__).resolve().parent;P=E.parent/'owner-dedupe-20261107'
s='''import NIN_ObserverFields
set_option autoImplicit false
noncomputable section
namespace AspisR1.NIR_SameLawInstance
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep
open AspisV8R19.MemoizedProgramLaw SCE_Experiment
variable {W A C Tx : Type} (L : Library W (Nat → Record))
    (copy : Heap (Nat → Record) → Nat → Payload → S2W_TrustedStd.Outcome (Nat → Record))
    (allocator : Allocator A) (base : DrvC_Installation.Configuration FIo_Install.W C)
    (err : C) (r : NP6_StdModel.Reservation)
    (n1 : S2W_ExtractionBoundary.First) (n2 : S2W_ExtractionBoundary.Second)
    (hashv : SdkC_Source.Parts → Result SdkC_Source.Digest) (a : Adversary A)
/-- Ruling (ao): recognition of the headline runtime; discharges no security obligation. -/
theorem realizes :
    NHZ_EXPERIMENT.Realizes (Tx := Tx) L copy allocator base err r n1 n2 hashv a
      (ARX_AdmittedRuntime.runtime (Tx := Tx) L copy allocator base err r n1 n2 hashv a) := by
  intro H
  rfl
/-- The admitted world's support criterion is the existing permitted_iff law,
not a new exporter or admission assumption. -/
theorem permitted_iff
    (extraction : S2W_DigestExtraction.AeneasExtraction
      (DrvC_Installation.sdk (FIp_Install.configuration err base r)) n1 n2 hashv)
    (H : Bytes → State) :
    ARX_AdmittedRuntime.permitted (Tx := Tx) L copy allocator base err r n1 n2 hashv a
      (eval H (ART_PartialAccount.account (FIp_Install.configuration err base r)
        hashv copy allocator CPH_Program.verifier a)) ↔
    Nonempty (ARU_Support.At (Tx := Tx) L copy allocator base err r n1 n2 hashv a H) :=
  ARX_AdmittedRuntime.permitted_iff L copy allocator base err r n1 n2 hashv a extraction H
#check AspisR1.NIN_Observer.canonical_from_initial
#check AspisR1.NIN_Observer.stored_public
#check AspisR1.NIN_Observer.outer_from_coverage
#check AspisR1.NIN_Observer.nested_from_outer
#check AspisR1.NIN_Observer.flag_from_results
#check AspisR1.NIN_Observer.accepted_iff
#print axioms realizes
#print axioms permitted_iff
end AspisR1.NIR_SameLawInstance
'''
(E/'NIR_SameLawInstance.lean').write_text(s)
(E/'NIR_COMBINED_IMPORT.lean').write_text('''import NGK_COMBINED_IMPORT
import NIM_COMBINED_IMPORT
import NIM_NHJ_COMBINED_IMPORT
import NIM_NHY_COMBINED_IMPORT
import NIG_COMBINED_IMPORT
import NIN_COMBINED_IMPORT
import NIR_SameLawInstance
#print axioms AspisR1.RPx_Deployed.deployed
#print axioms AspisR1.NIN_NativeInstance.from_native
#print axioms AspisR1.NIR_SameLawInstance.realizes
#print axioms AspisR1.NIR_SameLawInstance.permitted_iff
''')
for name in ['Driver','ProofDriver']:
 s=(P/f'NIM_{name}.lean').read_text();t=s.replace('NIM_','NIR_');(E/f'NIR_{name}.lean').write_text(t);(E/f'NIR_{name}.diff').write_text(''.join(difflib.unified_diff(s.splitlines(True),t.splitlines(True))))
(E/'NIR_batch.py').write_text((P/'NIM_batch.py').read_text().replace('NIM_','NIR_'))
roots=set(json.loads((P/'NIM_AUDIT_ROOTS_CORRECTED.json').read_text())['roots'])
for folder,prefix in [('l159-physical-20261107','NIN'),('slice-d-pair4-20261107','NIG')]:
 d=json.loads((E.parent/folder/f'{prefix}_AUDIT_ROOTS.json').read_text()); roots.update(d.get('roots',[r for group in d.get('groups',[]) for r in group]) if isinstance(d,dict)else d)
roots.update(['AspisR1.NIR_SameLawInstance.realizes','AspisR1.NIR_SameLawInstance.permitted_iff']);roots=sorted(roots)
# 32 batches permit exact full root coverage without any repeated unchanged audit.
n=32
(E/'NIR_AUDIT_ROOTS.json').write_text(json.dumps(dict(roots=roots,groups=[roots[i*len(roots)//n:(i+1)*len(roots)//n]for i in range(n)]),indent=1)+'\n')
(E/'NIR_AUDIT_MODULES.json').write_text(json.dumps([['NIR_COMBINED_IMPORT']for _ in range(n)],indent=1)+'\n')
b={}
for folder,prefix in [('owner-dedupe-20261107','NIM'),('l159-physical-20261107','NIN'),('slice-d-pair4-20261107','NIG')]:
 for line in (E.parent/folder/f'{prefix}_EXPECTED_IMPORTS.jsonl').read_text().splitlines():
  x=json.loads(line);b[x['module']]=x['imports']
for p in E.glob('NIR_*.lean'):b[p.stem]=list(dict.fromkeys(['Init']+re.findall(r'^import ([\w.]+)',p.read_text(),re.M)))
(E/'NIR_EXPECTED_IMPORTS.jsonl').write_text(''.join(json.dumps(dict(module=m,imports=v))+'\n'for m,v in sorted(b.items())))
print('NIR sources prepared; roots',len(roots))
