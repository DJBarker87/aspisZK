import R1Z.PDict_WireError
set_option autoImplicit false
noncomputable section
namespace R1Z.PDict_Typenum
open Aeneas Aeneas.Std Result ProverRwFull
variable [ExternalTypes]

-- These entries occur outside the successful proof-body cone. Native source
-- constants and ZST identities are checked in the cfg(kani) contract.
-- No UInt, GenericArray, SHA state, filesystem or effect type is instantiated.
@[reducible] def selected (ops : ExternalFuns) : ExternalFuns :=
  { PDict_WireError.selected ops with
    op163 := .ok 0#isize,
    op164 := .ok 0#i64,
    op165 := .ok 0#i32,
    op166 := .ok 0#i16,
    op167 := .ok 0#i8,
    op168 := .ok 0#usize,
    op169 := .ok 0#u64,
    op170 := .ok 0#u32,
    op171 := .ok 0#u16,
    op172 := .ok 0#u8,
    op173 := .ok 0#isize,
    op174 := .ok 0#i64,
    op175 := .ok 0#i32,
    op176 := .ok 0#i16,
    op177 := .ok 0#i8,
    op178 := .ok 0#usize,
    op179 := .ok 0#u64,
    op180 := .ok 0#u32,
    op181 := .ok 0#u16,
    op182 := .ok 0#u8,
    op183 := .ok (),
    op184 := fun x => .ok x,
    op188 := .ok true,
    op189 := .ok 1#u8,
    op190 := .ok (),
    op191 := .ok true,
    op192 := .ok 1#u8,
    op193 := .ok (),
    op194 := fun x => .ok x,
    op196 := .ok Ordering.eq,
    op197 := .ok Ordering.gt,
    op198 := .ok false,
    op199 := .ok 0#u8,
    op200 := .ok (),
    op201 := .ok false,
    op202 := .ok 0#u8,
    op203 := .ok (),
    op204 := fun x => .ok x }

theorem op163_installed (ops : ExternalFuns) :
    (selected ops).op163 = .ok 0#isize := rfl

theorem op164_installed (ops : ExternalFuns) :
    (selected ops).op164 = .ok 0#i64 := rfl

theorem op165_installed (ops : ExternalFuns) :
    (selected ops).op165 = .ok 0#i32 := rfl

theorem op166_installed (ops : ExternalFuns) :
    (selected ops).op166 = .ok 0#i16 := rfl

theorem op167_installed (ops : ExternalFuns) :
    (selected ops).op167 = .ok 0#i8 := rfl

theorem op168_installed (ops : ExternalFuns) :
    (selected ops).op168 = .ok 0#usize := rfl

theorem op169_installed (ops : ExternalFuns) :
    (selected ops).op169 = .ok 0#u64 := rfl

theorem op170_installed (ops : ExternalFuns) :
    (selected ops).op170 = .ok 0#u32 := rfl

theorem op171_installed (ops : ExternalFuns) :
    (selected ops).op171 = .ok 0#u16 := rfl

theorem op172_installed (ops : ExternalFuns) :
    (selected ops).op172 = .ok 0#u8 := rfl

theorem op173_installed (ops : ExternalFuns) :
    (selected ops).op173 = .ok 0#isize := rfl

theorem op174_installed (ops : ExternalFuns) :
    (selected ops).op174 = .ok 0#i64 := rfl

theorem op175_installed (ops : ExternalFuns) :
    (selected ops).op175 = .ok 0#i32 := rfl

theorem op176_installed (ops : ExternalFuns) :
    (selected ops).op176 = .ok 0#i16 := rfl

theorem op177_installed (ops : ExternalFuns) :
    (selected ops).op177 = .ok 0#i8 := rfl

theorem op178_installed (ops : ExternalFuns) :
    (selected ops).op178 = .ok 0#usize := rfl

theorem op179_installed (ops : ExternalFuns) :
    (selected ops).op179 = .ok 0#u64 := rfl

theorem op180_installed (ops : ExternalFuns) :
    (selected ops).op180 = .ok 0#u32 := rfl

theorem op181_installed (ops : ExternalFuns) :
    (selected ops).op181 = .ok 0#u16 := rfl

theorem op182_installed (ops : ExternalFuns) :
    (selected ops).op182 = .ok 0#u8 := rfl

theorem op183_installed (ops : ExternalFuns) :
    (selected ops).op183 = .ok () := rfl

theorem op184_installed (ops : ExternalFuns) (x : typenum.uint.UTerm) :
    (selected ops).op184 x = .ok x := rfl

theorem op188_installed (ops : ExternalFuns) :
    (selected ops).op188 = .ok true := rfl

theorem op189_installed (ops : ExternalFuns) :
    (selected ops).op189 = .ok 1#u8 := rfl

theorem op190_installed (ops : ExternalFuns) :
    (selected ops).op190 = .ok () := rfl

theorem op191_installed (ops : ExternalFuns) :
    (selected ops).op191 = .ok true := rfl

theorem op192_installed (ops : ExternalFuns) :
    (selected ops).op192 = .ok 1#u8 := rfl

theorem op193_installed (ops : ExternalFuns) :
    (selected ops).op193 = .ok () := rfl

theorem op194_installed (ops : ExternalFuns) (x : typenum.bit.B1) :
    (selected ops).op194 x = .ok x := rfl

theorem op196_installed (ops : ExternalFuns) :
    (selected ops).op196 = .ok Ordering.eq := rfl

theorem op197_installed (ops : ExternalFuns) :
    (selected ops).op197 = .ok Ordering.gt := rfl

theorem op198_installed (ops : ExternalFuns) :
    (selected ops).op198 = .ok false := rfl

theorem op199_installed (ops : ExternalFuns) :
    (selected ops).op199 = .ok 0#u8 := rfl

theorem op200_installed (ops : ExternalFuns) :
    (selected ops).op200 = .ok () := rfl

theorem op201_installed (ops : ExternalFuns) :
    (selected ops).op201 = .ok false := rfl

theorem op202_installed (ops : ExternalFuns) :
    (selected ops).op202 = .ok 0#u8 := rfl

theorem op203_installed (ops : ExternalFuns) :
    (selected ops).op203 = .ok () := rfl

theorem op204_installed (ops : ExternalFuns) (x : typenum.bit.B0) :
    (selected ops).op204 x = .ok x := rfl

#print axioms op163_installed
#print axioms op164_installed
#print axioms op165_installed
#print axioms op166_installed
#print axioms op167_installed
#print axioms op168_installed
#print axioms op169_installed
#print axioms op170_installed
#print axioms op171_installed
#print axioms op172_installed
#print axioms op173_installed
#print axioms op174_installed
#print axioms op175_installed
#print axioms op176_installed
#print axioms op177_installed
#print axioms op178_installed
#print axioms op179_installed
#print axioms op180_installed
#print axioms op181_installed
#print axioms op182_installed
#print axioms op183_installed
#print axioms op184_installed
#print axioms op188_installed
#print axioms op189_installed
#print axioms op190_installed
#print axioms op191_installed
#print axioms op192_installed
#print axioms op193_installed
#print axioms op194_installed
#print axioms op196_installed
#print axioms op197_installed
#print axioms op198_installed
#print axioms op199_installed
#print axioms op200_installed
#print axioms op201_installed
#print axioms op202_installed
#print axioms op203_installed
#print axioms op204_installed
end R1Z.PDict_Typenum
