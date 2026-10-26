import R1Z.ProverRw18ContextTotal
set_option autoImplicit false
noncomputable section
namespace R1Z.ProverRw18FixtureSamples
open Aeneas Aeneas.Std Result ProverRwFull
open ProverRw18InlineContext
-- These are reified samples from the measured native fixture run, not a
-- supplied security-model interpretation or a proof-byte/audit comparison.

def transfer_values : Array U32 16#usize := ⟨[1946206803#u32,48538015#u32,696994726#u32,1059389847#u32,1447429399#u32,645037116#u32,548601256#u32,1757160991#u32,810523887#u32,1816883202#u32,718849816#u32,1097309788#u32,53346212#u32,255319321#u32,163548979#u32,897757192#u32],by decide⟩
def transfer_tag : U32 := 1124073472#u32
def transfer_lambda : Q := ⟨⟨7#u32,11#u32⟩,⟨17#u32,19#u32⟩⟩

def withdrawal_values : Array U32 16#usize := ⟨[1946206803#u32,48538015#u32,696994726#u32,1059389847#u32,1447429399#u32,645037116#u32,548601256#u32,1757160991#u32,810523887#u32,1816883202#u32,718849816#u32,1097309788#u32,53346212#u32,255319321#u32,163548979#u32,897757192#u32],by decide⟩
def withdrawal_tag : U32 := 1124073472#u32
def withdrawal_lambda : Q := ⟨⟨7#u32,11#u32⟩,⟨17#u32,19#u32⟩⟩

variable [ExternalTypes]

theorem transfer_context (ops : ExternalFuns) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      transfer_tag (Array.to_slice transfer_values) transfer_lambda =
      PV_RW_CompressClosed.owned transfer_tag (Array.to_slice transfer_values) transfer_lambda :=
  ProverRw18ContextTotal.arity16 ops transfer_tag transfer_values transfer_lambda

theorem transfer_nonempty (ops : ExternalFuns) :
    ∃ out, @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      transfer_tag (Array.to_slice transfer_values) transfer_lambda=ok out :=
  ProverRw18ContextTotal.total ops transfer_tag (Array.to_slice transfer_values) transfer_lambda
#print axioms transfer_context
#print axioms transfer_nonempty

theorem withdrawal_context (ops : ExternalFuns) :
    @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      withdrawal_tag (Array.to_slice withdrawal_values) withdrawal_lambda =
      PV_RW_CompressClosed.owned withdrawal_tag (Array.to_slice withdrawal_values) withdrawal_lambda :=
  ProverRw18ContextTotal.arity16 ops withdrawal_tag withdrawal_values withdrawal_lambda

theorem withdrawal_nonempty (ops : ExternalFuns) :
    ∃ out, @ProverRw18ContextCompression.compress _ (PV_CurrentScaleInstall.selected ops)
      withdrawal_tag (Array.to_slice withdrawal_values) withdrawal_lambda=ok out :=
  ProverRw18ContextTotal.total ops withdrawal_tag (Array.to_slice withdrawal_values) withdrawal_lambda
#print axioms withdrawal_context
#print axioms withdrawal_nonempty
end R1Z.ProverRw18FixtureSamples
