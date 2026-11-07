"""One row and its isolated, literal W4 package comparison; no mixed cohort."""
import sys,pathlib,subprocess,json,hashlib,lzma
L=pathlib.Path('evidence/pv-lib-20261107/lane-SPEC');n=int(sys.argv[1]);a=int(sys.argv[2]);b=int(sys.argv[3]);arity={170:2,17:2,5:0,2:0}[n]
ns=f'PV_LIB_SPEC_F{n}Full';oldmod='PV_FN_THREAD_f170_OriginalStatement' if n==170 else f'PV_FN_THREAD_f{n}OriginalStatement';oldns='PV_FN_THREAD_f170' if n==170 else f'PV_FN_THREAD_f{n}Contract'
oldsrc=subprocess.check_output(['git','show','ce2f78097fa7:lean/'+oldmod+'.lean']);spec=subprocess.check_output(['git','show',f'5e397cb3878:evidence/pv-lib-20261107/PSPEC_thread_f{n}.md'],text=True);post=spec.split('## Post, frame and complete arms')[1].split('Every returned')[0].strip().replace('`','')
text=f'''import PV_LIB_SPEC_F6Full
set_option autoImplicit false
noncomputable section
namespace {ns}
open PV_STX_Machine PV_STX2_Syntax PV_STX2_Store PV_STX2_SliceMachine
open PV_LIB_SPEC_D984 PV_LIB_SPEC_Row
abbrev Input := PV_LIB_SPEC_Row.Input
abbrev MachineSpec := PV_LIB_SPEC_Full.MachineSpec
/-- The row's OWN entry, all source arguments and valid registered references,
OWNER/header invariants and numbering. No callback success, write-definedness,
replacement Effects dictionary, pending-world frame or future read. -/
def Pre (r : Runtime) (i : Input) : Prop :=
  PV_LIB_SPEC_Row.Pre PV_THR2_F{n}.live {arity} r i
/-- {post}
Use source-encoded Option/Result/ControlFlow values, not a world-dependent
opaque marker. All responses remain in the domain. The final table parameter
includes source writes289 and any boxed Cell/atomic state found under D984. -/
def Post (table : FullStoreActionTable) (r : Runtime) (i : Input)
    (candidate : Nat → State) : Prop :=
  PV_LIB_SPEC_Full.Post table r PV_THR2_F{n}.live i candidate
def Contract (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  ∀ m i, MachineSpec table r m → Pre r i → Post table r i (implementation m i)
/-- A paired comparison, not a cross-cohort import or implication proof.
packageContract is the literal typed PackageContract of F{n}PackageComparison
in the original W4 cohort. It is NOT a premise of the new Contract. -/
def Comparison (packageContract : Prop) (table : FullStoreActionTable) (r : Runtime)
    (implementation : Machine → Input → Nat → State) : Prop :=
  packageContract ∧ Contract table r implementation
#print axioms MachineSpec
#print axioms Pre
#print axioms Post
#print axioms Contract
#print axioms Comparison
end {ns}
'''
p=pathlib.Path('lean')/(ns+'.lean');assert not p.exists();p.write_text(text)
(L/f'SESSION5_FULL_PACKAGE_f{n}.json').write_text(json.dumps({'revision':'ce2f78097fa7e3cabc7b66fdfb9445c067917831','module':oldmod,'source_sha256':hashlib.sha256(oldsrc).hexdigest(),'new_module':ns,'package_comparison':f'PV_LIB_SPEC_F{n}PackageComparison','comparison_kind':'paired isolated typed statements, parameterized conjunction; NO equivalence/transport theorem or combined replay claimed','differences':spec.split('## Comparison to current package statements')[1].split('## Rejection example')[0].strip()},indent=2)+'\n');(L/f'PACKAGE_f{n}_SOURCE.lean.xz').write_bytes(lzma.compress(oldsrc))
subprocess.run(['python3',str(L/'finish_statement.py'),ns,str(a),'w3'],check=True)
# Only after the whole new statement compiles, write the old-cohort comparison.
ns=f'PV_LIB_SPEC_F{n}PackageComparison';prefix=oldns+'.';pres='PreNumbered' if n==170 else 'Pre';machine='OriginalMachineSpec' if n==170 else 'MachineSpecWithOriginal';contract='OriginalContract' if n==170 else 'ContractWithOriginal'
text=f'''import {oldmod}
set_option autoImplicit false
noncomputable section
namespace {ns}
/-- Literal declarations from W4 ce2f78097fa7; source hash
{hashlib.sha256(oldsrc).hexdigest()}. This partition never imports the new
W3-cohort statement. The paired manifest names its exact counterpart. -/
abbrev PackagePre := @{prefix}{pres}
abbrev PackageMachineSpec := @{prefix}{machine}
abbrev PackagePost := @{prefix}Post
abbrev PackageContract := @{prefix}{contract}
/-- The complete old contract TYPE is retained by the alias, including all
pending dependency arguments. A newContract parameter is a statement target,
not a proved new row, assumed leaf law or added endpoint hypothesis. -/
def Comparison (newContract : Prop) : Prop := newContract
#print axioms PackagePre
#print axioms PackageMachineSpec
#print axioms PackagePost
#print axioms PackageContract
#print axioms Comparison
end {ns}
'''
(pathlib.Path('lean')/(ns+'.lean')).write_text(text)
subprocess.run(['python3',str(L/'finish_statement.py'),ns,str(b),'w4'],check=True)
