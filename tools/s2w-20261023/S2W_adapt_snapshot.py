"""Replace generated external templates with explicit carrier/operation parameters.
No body branches, data projections, or operation calls are removed.
"""
from pathlib import Path
import re,json,hashlib
R=Path(__file__).resolve().parents[2]; E=R/'evidence/s2w-20261023/snapshot-emission'; O=R/'docs/research/100bit-spend-path-20261013/lean/S2W_Snapshot.lean'
raw=(E/'Funs.lean.txt').read_text();start=raw.index('def r1_pool_adapter.owned.snapshot');body=raw[start:raw.index('\nend S2W_Snapshot')]
changes={'def r1_pool_adapter.owned.snapshot':'def snapshot (C : Carriers) (ops : Ops C)', 'solana_account_info.AccountInfo.try_borrow_data':'ops.borrow', 'core.cell.Ref.Insts.CoreOpsDerefDeref.deref':'ops.deref','solana_program_error.ProgramError.Insts.CoreCloneClone.clone':'ops.cloneError','solana_account_info.AccountInfo':'AccountInfo C','r1_pool_adapter.owned.OwnedAccount':'OwnedAccount','solana_program_error.ProgramError':'PE'}
for old,new in changes.items():body=body.replace(old,new)
header='''import AdapterRwTypes

/-! Mechanical native snapshot emission, with external SDK carriers/operations
as parameters. No SDK interpretation or native heap-frame instance is asserted.
Aeneas erases implicit drops; their runtime join is a separate obligation. -/
set_option autoImplicit false
noncomputable section
namespace AspisR1.S2W.Snapshot
open Aeneas Aeneas.Std Result
abbrev PE := AdapterRw.solana_program_error.ProgramError
abbrev OwnedAccount := AdapterRw.r1_pool_adapter.owned.OwnedAccount

structure Carriers where
  RefCell : Type → Type
  Ref : Type → Type
  Rc : Type → Type

structure AccountInfo (C : Carriers) where
  key : AdapterRw.solana_pubkey.Pubkey
  lamports : C.Rc (C.RefCell U64)
  data : C.Rc (C.RefCell (Slice U8))
  owner : AdapterRw.solana_pubkey.Pubkey
  rent_epoch : U64
  is_signer : Bool
  is_writable : Bool
  executable : Bool

structure Ops (C : Carriers) where
  borrow : AccountInfo C → Result ((core.result.Result (C.Ref (Slice U8)) PE) ×
    (core.result.Result (C.Ref (Slice U8)) PE → Unit))
  deref : C.Ref (Slice U8) → Result (Slice U8)
  cloneError : PE → Result PE

'''
body=body.replace('PE.InvalidAccountData','AdapterRw.solana_program_error.ProgramError.InvalidAccountData')
O.write_text(header+body+'\n#print axioms snapshot\nend AspisR1.S2W.Snapshot\nend\n')
(E/'adaptation.json').write_text(json.dumps({'raw_sha256':hashlib.sha256(raw.encode()).hexdigest(),'adapted_sha256':hashlib.sha256(O.read_bytes()).hexdigest(),'replacements':changes,'type_transport':'AccountInfo generated fields preserved with explicit RefCell/Ref/Rc carriers; identical PE and OwnedAccount reuse AdapterRwTypes; no function body edit beyond listed substitutions','qualification':'Uninstalled SDK operation parameters; not native effect/guard/provenance refinement'},indent=2)+'\n')
