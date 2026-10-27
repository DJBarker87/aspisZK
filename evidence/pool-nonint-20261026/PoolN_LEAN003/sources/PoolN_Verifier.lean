import Hist_InitialZero
import Hist_ReaderAuthority
import Hiq_LifecycleRejection
set_option autoImplicit false
noncomputable section
namespace AspisR1.PoolN_Verifier
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers

/-- Exact first nonzero-byte error of the extracted V1 freshness gate.
No hash, encoding or verifier child is called by this gate. -/
theorem V1_occupied_gate (bytes : Slice U8) (head : U8)
    (nonempty : 0 < bytes.val.length)
    (read : Slice.index_usize bytes 0#usize = ok head) (nonzero : head ≠ 0#u8) :
    AdapterRw.r1_pool_adapter.owned.require_zero bytes =
      ok (.Err AdapterRw.solana_program_error.ProgramError.AccountAlreadyInitialized) :=
  Hist_ZeroReject.reject bytes head nonempty read nonzero

/-- Actual extracted V1 cannot return an accepted saved CP on occupied original
account2. This includes all earlier rejection paths, without assuming that the
zero guard is reached. Wrapper/source/runtime boundaries remain the inherited
D189 boundaries; this is not a new claim about arbitrary SDK representations. -/
theorem V1_occupied_reject (e : Entry) (ops : AdapterRw.Ops)
    (program : S2W_ExtractionBoundary.Program) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (head : U8) (nonempty : 0 < (e.buffers (e.handles 2).1).val.length)
    (read : Slice.index_usize (e.buffers (e.handles 2).1) 0#usize = ok head)
    (nonzero : head ≠ 0#u8) :
    AdapterRw.r1_pool_adapter.owned.stage1_owned ops program e.first data ≠ ok (.Ok saved) :=
  Hist_InitialZero.no_reinitialize e ops program data saved head nonempty read nonzero

/-- Accepted V2 wrapper returns the complete original heap, not merely equal
checkpoint roots. This reuses the already checked wrapper interpretation and
retains its allocator/native source boundary. -/
theorem V2_frame {A : Type} (native : S2W_ExtractionBoundary.Second)
    (allocator : Allocator A) (e : Entry) (program : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (state final : A)
    (after : Heap (Nat → Record))
    (accepted : second native allocator e program data slot state = ok (.Ok (after,final))) :
    after = e.heap :=
  (second_accepted native allocator e program data slot state final after accepted).2

/-- Disabled loader/lifecycle routes are excluded by the admitted release route;
this does not assert a new whole-runtime effect law. -/
theorem disabled_admission (data : Slice U8) (tag : U8)
    (tagged : tag = 1#u8 ∨ tag = 2#u8 ∨ tag = 4#u8 ∨ tag = 5#u8 ∨ tag = 6#u8)
    (head : data.val.head? = some tag) : Hiq_ReleaseRoute.route data = .reject :=
  Hiq_LifecycleRejection.rejected data tag tagged head

#print axioms V1_occupied_gate
#print axioms V1_occupied_reject
#print axioms V2_frame
#print axioms disabled_admission
end AspisR1.PoolN_Verifier
end
