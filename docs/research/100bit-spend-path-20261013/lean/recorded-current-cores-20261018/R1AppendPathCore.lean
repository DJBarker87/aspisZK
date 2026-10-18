import R1AppendFrozenCore
import R0P.Digest
import R0P.Semantics

/-! The twenty literal append gates determine a public root and carry node.
The recurrence uses the frozen empty-root table exactly as the gates do;
its equality with recursively generated empty roots is a separate obligation.
No exclusion of the full-tree last insertion is introduced. -/
set_option autoImplicit false
namespace AspisR1.AppendPath
open R0P
variable {K : Type} [Field K]

def step (pub : Public K) (level : Fin 20) (cur : Digest K) : Digest K :=
  if digestBitZero pub level then nodeCompress cur (AppendNode.frozenEmpty level.castSucc)
  else nodeCompress (pub.snapshotFrontier level) cur

def pathPrefix (pub : Public K) (leaf : Digest K) : Nat → Digest K
  | 0 => leaf
  | n+1 => if h : n < 20 then step pub ⟨n, h⟩ (pathPrefix pub leaf n)
    else pathPrefix pub leaf n

end AspisR1.AppendPath


set_option pp.universes true in
#check @AspisR1.AppendPath.step

#print AspisR1.AppendPath.step
#print axioms AspisR1.AppendPath.step

#print AspisR1.AppendPath.pathPrefix
#print axioms AspisR1.AppendPath.pathPrefix
