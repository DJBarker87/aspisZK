import R1Z.PV_RunJoin_SemanticCompact40
set_option autoImplicit false
noncomputable section
namespace R1Z.PV_RunJoin_SemanticDomain40
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

def after (at1 size : Usize) : Usize :=
  Usize.wrapping_add (Usize.wrapping_add at1 5#usize) size

def raw (logical : Slice U8) (at1 size : Usize) : List U8 :=
  (logical.val.drop at1.val).take 5 ++ (logical.val.drop (at1.val+5)).take size.val

def compact (logical : Slice U8) (at1 size : Usize) (n : Nat) : List U8 :=
  (logical.val.drop at1.val).take 5 ++
    PV_RunJoin_SemanticCompact40.low ((logical.val.drop (at1.val+5)).take size.val) n

/-- A source byte domain only: the exact row shape, bounds, high-byte
canonicality, source successor counters, and end cursor. No loop Result,
success assumption, or desired model equality occurs in its constructors. -/
inductive Domain (ops : ExternalFuns) (logical : Slice U8) (count : U8) :
    Usize → U8 → List (List U8) → Prop where
  | nil (at1 : Usize) (row : U8) (stop : count≤row) (last : at1=Slice.len logical) :
      Domain ops logical count at1 row []
  | copy (at1 size : Usize) (row tag : U8) (rest : List (List U8))
      (more : row<count)
      (shape : @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) row=.ok (some (tag,size)))
      (small : row.val<14) (bound : at1.val+5+size.val≤logical.length)
      (tail : Domain ops logical count (after at1 size) (U8.wrapping_add row 1#u8) rest) :
      Domain ops logical count at1 row (raw logical at1 size::rest)
  | compact (at1 size : Usize) (row tag : U8) (n : Nat) (rest : List (List U8))
      (more : row<count)
      (shape : @r1_wire.row_shape _ (ProverRwP6BodyCandidate.selected ops) row=.ok (some (tag,size)))
      (large : 14≤row.val) (sizeval : size.val=32*n)
      (bound : at1.val+5+size.val≤logical.length)
      (zero : PV_RunJoin_HighDomain40.HighZero
        ((logical.val.drop (at1.val+5)).take size.val))
      (tail : Domain ops logical count (after at1 size) (U8.wrapping_add row 1#u8) rest) :
      Domain ops logical count at1 row (compact logical at1 size n::rest)
#print Domain
end R1Z.PV_RunJoin_SemanticDomain40
