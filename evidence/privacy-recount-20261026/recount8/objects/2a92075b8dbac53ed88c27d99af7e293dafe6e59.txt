import R1Z.ProverRwSuccessParser
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRwSuccessHashes
open Aeneas Aeneas.Std Result ProverRwFull
abbrev Hash := Slice (Slice U8) → Result (Array U8 32#usize)
def leafFrame (tag : U8) (values : Slice U8) : Slice (Slice U8) :=
  Array.to_slice (Array.make 2#usize
    [Array.to_slice (Array.make 2#usize [16#u8,tag]),values])
def leaf (hash : Hash) (tag : U8) (values : Slice U8) : Result (Array U8 32#usize) :=
  hash (leafFrame tag values)
def parentFrame (left right : Array U8 32#usize) : Slice (Slice U8) :=
  Array.to_slice (Array.make 3#usize
    [Array.to_slice (Array.make 1#usize [18#u8]),Array.to_slice left,Array.to_slice right])
def parent {H : Type} (inst : aspis_core.digest.Digest32 H) (hash : H)
    (left right : Array U8 32#usize) : Result (Array U8 32#usize) :=
  inst.digest hash (parentFrame left right)
variable [ExternalTypes]
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  {ProverRwSuccessParser.selected ops with op84 := leaf,op246 := parent}

theorem leaf_source (ops : ExternalFuns) (hash : Hash) (tag : U8) (values : Slice U8) :
    (selected ops).op84 hash tag values = hash (leafFrame tag values) := rfl

theorem parent_source (ops : ExternalFuns) {H : Type}
    (inst : aspis_core.digest.Digest32 H) (hash : H) (left right : Array U8 32#usize) :
    (selected ops).op246 inst hash left right = inst.digest hash (parentFrame left right) := rfl

theorem leaf_failure (ops : ExternalFuns) (hash : Hash) (tag : U8) (values : Slice U8)
    (error : Aeneas.Std.Error) (bad : hash (leafFrame tag values) = .fail error) :
    (selected ops).op84 hash tag values = .fail error := bad

theorem leaf_divergence (ops : ExternalFuns) (hash : Hash) (tag : U8) (values : Slice U8)
    (diverges : hash (leafFrame tag values) = .div) :
    (selected ops).op84 hash tag values = .div := diverges
#print axioms leaf_source
#print axioms parent_source
#print axioms leaf_failure
#print axioms leaf_divergence
end R1Z.ProverRwSuccessHashes
