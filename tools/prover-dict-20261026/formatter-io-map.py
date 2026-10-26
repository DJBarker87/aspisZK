from pathlib import Path
import re
r=Path(__file__).resolve().parents[2];p=r/'docs/research/v8-r0-zk-20261009/lean/R1Z/PDict_FormatterIOMap.lean';ext=(r/'docs/research/100bit-spend-path-20261013/lean/prover-rw-20261023/ProverRwFullExternalFuns.lean').read_text()
a={int(i):n for n,i in re.findall(r'(?m)^abbrev\s+([\w.]+)[^\n]*@ExternalFuns\.op(\d+)',ext)}
s='''import R1Z.PDict_FormatterStorePath
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_FormatterIOMap
open Aeneas Aeneas.Std ProverRwFull PDict_FormatterTypeMaps PDict_FormatterDictionaryMap
'''
for i in [14,15,19,20,21,22,23,24,25,26,27,28,29,30,31,261]:
 n=a[i];s+=f'\ntheorem io{i} (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :\n    @{n} (types b F) (selected b F ops) = @{n} b ops := rfl\n#print axioms io{i}\n'
s+='''
theorem sync_directory (b : ExternalTypes) (F : Type) (ops : @ExternalFuns b) :
    @aspis_prover.state_only_entropy.sync_directory (types b F) (selected b F ops) =
    @aspis_prover.state_only_entropy.sync_directory b ops := by
  delta aspis_prover.state_only_entropy.sync_directory
  delta aspis_prover.state_only_entropy.sync_directory.match_1
  rfl
#print axioms sync_directory
end R1Z.PDict_FormatterIOMap
''';p.write_text(s)
