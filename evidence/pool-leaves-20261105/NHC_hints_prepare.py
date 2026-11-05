from pathlib import Path
import json,hashlib,re
E=Path(__file__).resolve().parent;D=E/'NHC_Hints';D.mkdir(exist_ok=True);raw=E/'NHC_E002_extracted/NHC_Hints';records=[]
audit='''\nrun_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
'''
for name in ['Types','Funs']:
 before=(raw/(name+'.lean.txt')).read_text();after=before
 if name=='Types':
  start=after.index('/-- [solana_program_error::ProgramError]');end=after.index('/-- [aspis_pool::pair_forest::PoolV1PairForestTerminalBumpHintsV1]')
  after=after[:start]+after[end:];after='import Lean\nimport NGK_COMBINED_IMPORT\n'+after
 else:after='import Lean\n'+after.replace('solana_program_error.ProgramError','AdapterRw.solana_program_error.ProgramError')
 after+=audit;(D/(name+'.lean')).write_text(after)
 records.append(dict(input=str(raw/(name+'.lean.txt')),input_sha256=hashlib.sha256(before.encode()).hexdigest(),output=str(D/(name+'.lean')),output_sha256=hashlib.sha256(after.encode()).hexdigest(),before=before,after=after))
(D/'FunsExternal.lean').write_text('''import NHC_Hints.Types
open Aeneas Aeneas.Std Result
namespace NHC_Hints
/-- Standard Option elimination, implemented rather than assumed. -/
def core.option.Option.ok_or {T E : Type} (x : Option T) (e : E) : Result (Aeneas.Std.core.result.Result T E) :=
  ok (match x with | none => .Err e | some v => .Ok v)
/-- Frozen pair_forest.rs:110, exactly four hint bytes. -/
def pair_forest.POOL_V1_PAIR_FOREST_TERMINAL_BUMP_HINT_BYTES : Result Usize := ok 4#usize
end NHC_Hints
''')
(E/'NHC_HINTS_PROVENANCE.json').write_text(json.dumps(dict(extraction='NHC_E002',adaptations=['canonical ProgramError owner, exact constructor carrier retained','implemented two external primitive definitions; no axioms','print all local theorems'],files=records),indent=1)+'\n')
