import Lean
import NGF_NEY_ResultStores

set_option autoImplicit false
noncomputable section
namespace NGF_NEY_ResultProjection
open Aeneas Aeneas.Std

def expected (out : Array U8 792#usize) (master selected nullifier : Array U8 32#usize)
    (kind lane : U8) (afterstate : Array U8 688#usize) (k : Nat) : Option U8 :=
  if 104≤k ∧ k<792 then afterstate.val[k-104]?
  else if 72≤k ∧ k<104 then nullifier.val[k-72]?
  else if 40≤k ∧ k<72 then selected.val[k-40]?
  else if 8≤k ∧ k<40 then master.val[k-8]?
  else if k=7 then some lane
  else if k=6 then some 1#u8
  else if k=5 then some kind
  else if k=4 then some 1#u8
  else if k<4 then ([65#u8,83#u8,82#u8,56#u8] : List U8)[k]?
  else out.val[k]?

theorem writes_spec (out : Array U8 792#usize) (master selected nullifier : Array U8 32#usize)
    (kind lane : U8) (afterstate : Array U8 688#usize) (k : Nat) :
    NGF_NEY_ResultStores.writes out master selected nullifier kind lane afterstate k =
      expected out master selected nullifier kind lane afterstate k := by
  simp only [NGF_NEY_ResultStores.writes,expected,KMX_CopyMeaning.loop_spec,KMX_CopyMeaning.write,
    Nat.zero_le,true_and,Nat.sub_zero]
  rfl

theorem stores_spec (out : Array U8 792#usize) (master selected nullifier : Array U8 32#usize)
    (kind lane : U8) (afterstate : Array U8 688#usize) (k : Nat) :
    (AspisR1.S2K.ResultEncoding.stores out master selected nullifier kind lane afterstate).val[k]? =
      expected out master selected nullifier kind lane afterstate k := by
  change NGF_NEY_ResultStores.observe _ k = _
  rw [NGF_NEY_ResultStores.stores_observe,writes_spec]

#print axioms writes_spec
#print axioms stores_spec
end NGF_NEY_ResultProjection

run_cmd do
 let env ← Lean.getEnv
 env.constants.toList.forM fun (n, ci) => do
  if ci.isTheorem && (env.getModuleIdxFor? n).isNone then
   Lean.Elab.Command.elabCommand (← `(command| #print axioms $(Lean.mkIdent n)))
