import Hist_ArgumentCuts
import RPz7_GExq_AccountExperiment
set_option autoImplicit false
noncomputable section
namespace AspisR1.Hiq_ByteSelection
open Aeneas Aeneas.Std Result MultiproofConeCanonical S2W_NativeConsolidation
open AspisV8R19.DuplexFrames AspisV8R19.SourceDuplexStep

/-- Total deterministic projection of the original source account bytes.
Rejecting/missing inputs use empty bytes, retaining all source prefixes. -/
def account (ops : AdapterRw.Ops) (accounts : S2W_ExtractionBoundary.Accounts)
    (slot : Usize) : Bytes :=
  match Slice.index_usize accounts slot with
  | .ok a => match AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops a with
    | .ok (.Ok bytes) => bytesOf bytes.val
    | _ => []
  | _ => []

def public2 (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (accounts : S2W_ExtractionBoundary.Accounts) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) : Bytes :=
  match AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id accounts data slot with
  | .ok (.Ok v) => match ops.op22 v.statement with
    | .ok (.Ok encoded) => bytesOf encoded.val
    | _ => []
  | _ => []

def select {A : Type} (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (out : GExq_AccountExperiment.Outcome A) :
    R9PoolRuntimeBinding.Inputs × R9PoolRuntimeBinding.Inputs :=
  (⟨(account ops out.1.entry.first 0#usize).drop 688,
    account ops out.1.entry.first 1#usize⟩,
   match out.2.2 with
   | none => ⟨[],[]⟩
   | some (next,_) => ⟨(account ops (next.entry.second S2W_D189Wrappers.secondSizes) 0#usize).drop 688,
     public2 ops id (next.entry.second S2W_D189Wrappers.secondSizes) next.data next.slot⟩)

theorem account_read (ops : AdapterRw.Ops) (accounts : S2W_ExtractionBoundary.Accounts)
    (slot : Usize) (a : AdapterRw.Cuts.Account) (bytes : Slice U8)
    (indexed : Slice.index_usize accounts slot = ok a)
    (read : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops a = ok (.Ok bytes)) :
    account ops accounts slot = bytesOf bytes.val := by
  simp only [account,indexed,read]

theorem public2_read (ops : AdapterRw.Ops) (id : S2W_ExtractionBoundary.Program)
    (accounts : S2W_ExtractionBoundary.Accounts) (data : Slice U8)
    (slot : S2W_ExtractionBoundary.Slot) (v : AdapterRw.r1_pool_adapter.ValidatedAsqa)
    (encoded : Array U8 1880#usize)
    (validation : AdapterRw.r1_pool_adapter.owned.validate_asq8 ops id accounts data slot = ok (.Ok v))
    (encoding : ops.op22 v.statement = ok (.Ok encoded)) :
    public2 ops id accounts data slot = bytesOf encoded.val := by
  simp only [public2,validation,encoding]

#print axioms account_read
#print axioms public2_read
end AspisR1.Hiq_ByteSelection
end
