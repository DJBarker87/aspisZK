-- PCWR_ item 1: AdapterRwModel source re-pointed to evidence/adapter-rw-20261023/lean-040 (sha c6aa4d35, the l187 plan source).
-- This file only inspects the COMPILED gate constants (L187 closure, module AdapterRwModel): the Pubkey PartialEq instance.
-- No statement here depends on the repository text; the equalities of PCWL_ (w4, w5, w7) are against the same compiled constants.
import Aeneas
import AdapterRwModel
open Aeneas Aeneas.Std Result ControlFlow Error
namespace PRVEq.AdapterRwModel_r1
open AdapterRw

#print AdapterRw.solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey

theorem pubkey_ne_is_trait_default (ops : Ops) :
    (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops).ne
      = core.cmp.PartialEq.ne.trait_default (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops) := rfl
#print axioms pubkey_ne_is_trait_default

theorem pubkey_eq_is_op36 (ops : Ops) :
    (solana_pubkey.Pubkey.Insts.CoreCmpPartialEqPubkey ops).eq = ops.op36 := rfl
#print axioms pubkey_eq_is_op36

end PRVEq.AdapterRwModel_r1
