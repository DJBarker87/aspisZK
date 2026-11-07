from pathlib import Path
import re
E=Path(__file__).resolve().parent
src=(E/'NMT_stage1_owned.Funs.lean').read_text()
vars=src[src.index('-- Opaque callees'):src.index('/-- Trait implementation:')]
vs=re.findall(r'variable \(NMT_call_(\d+) : ([\s\S]*?)\)\n\n',vars)
assert len(vs)==17
header='''import NMT_stage1_owned.Funs
import NMT_RSL_TX1_345
set_option autoImplicit false
noncomputable section
namespace NMT_345
open Aeneas Aeneas.Std Result NMT_stage1_owned
abbrev PE := NMT_stage1_owned.solana_program_error.ProgramError
abbrev Account := NMT_stage1_owned.r1_pool_adapter.owned.OwnedAccount
abbrev Key := NMT_stage1_owned.solana_pubkey.Pubkey
abbrev Ret := core.result.Result (alloc.vec.Vec U8) PE
/-- Fresh E003 opaque interfaces. SUPPORT ONLY, never a row-root hypothesis.
Each field must be concretely installed before a candidate exists. -/
structure Calls where
'''
for n,ty in vs:header+=f' c{n} : '+ty.replace('\n','\n  ')+'\n'
header+='''/-- A single parent state retains original arguments, ambient world and
ordered effect prefix. Phase extensions add locals without projecting world. -/
structure Parent (W : Type) where
 program : Key
 accounts : Slice Account
 data : Slice U8
 world : W
 events : List RSL.Event

def emitted {W : Type} (c : Calls) (s : Parent W) : Result Ret :=
 NMT_stage1_owned.r1_pool_adapter.owned.stage1_owned '''+' '.join('c.c'+str(n) for n in range(17))+''' s.program s.accounts s.data

end NMT_345
'''
(E/'NMT_345Context.lean').write_text(header)
