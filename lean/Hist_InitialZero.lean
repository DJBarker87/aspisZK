import Hist_EntryZero
import Hist_ZeroReject
import S2W_D189Entry
set_option autoImplicit false
namespace AspisR1.Hist_InitialZero
open Aeneas Aeneas.Std Result
open S2W_D189Entry

/-- The zero gate uses the checkpoint's actual original entry buffer. -/
theorem accepted_zero (e : Entry) (ops : AdapterRw.Ops)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (accepted : AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e.first data = ok (.Ok saved)) :
    AdapterRw.r1_pool_adapter.owned.require_zero (e.buffers (e.handles 2).1) = ok (.Ok ()) := by
  obtain ⟨ca,bytes,index,read,zero⟩ := Hist_EntryZero.zero_gate ops program e.first data saved accepted
  have same := Result.ok.inj (index.symm.trans (first_index e).2.2)
  subst ca
  have size := checkpoint_size e ops program data saved accepted
  change (e.buffers (e.handles 2).1).val.length = 1768 at size
  have projected : AdapterRw.r1_pool_adapter.owned.OwnedAccount.data ops
      (e.snapshot 2 1768 1768) = ok (.Ok (e.buffers (e.handles 2).1)) := by
    simp only [Entry.snapshot,size,or_self,if_true,
      AdapterRw.r1_pool_adapter.owned.OwnedAccount.data,alloc.vec.Vec.deref]
    congr 2
  have eq := core.result.Result.Ok.inj (Result.ok.inj (read.symm.trans projected))
  rw [eq] at zero
  exact zero

/-- An initialized checkpoint with a nonzero first byte cannot be the target
of another accepted stage1. This is a source theorem, not history protection
assumed as a structure field. -/
theorem no_reinitialize (e : Entry) (ops : AdapterRw.Ops)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (head : U8) (nonempty : 0 < (e.buffers (e.handles 2).1).val.length)
    (read : Slice.index_usize (e.buffers (e.handles 2).1) 0#usize = ok head)
    (nonzero : head ≠ 0#u8) :
    AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e.first data ≠ ok (.Ok saved) := by
  intro accepted
  have zero := accepted_zero e ops program data saved accepted
  rw [Hist_ZeroReject.reject _ head nonempty read nonzero] at zero
  cases zero

#print axioms accepted_zero
#print axioms no_reinitialize
end AspisR1.Hist_InitialZero
