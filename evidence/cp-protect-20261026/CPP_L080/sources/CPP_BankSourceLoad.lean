import CPP_BankCache
import Hir_ReaderEntry
set_option autoImplicit false
noncomputable section
namespace AspisR1.CPP_BankSourceLoad
open Aeneas Aeneas.Std Result S2Trust S2W_D189Entry S2W_D189Wrappers Hist_Store Hist_RuntimeEntry

theorem writer_live (ops : AdapterRw.Ops) (e : Entry)
    (id : S2W_ExtractionBoundary.Program) (data : Slice U8) (saved : alloc.vec.Vec U8)
    (account : CPP_BankCache.Account)
    (source : AdapterRw.r1_pool_adapter.owned.stage1_owned ops id e.first data = ok (.Ok saved))
    (bankInput : e.buffers (e.handles 2).1 = CPP_BankCache.image account) :
    0 < account.record.lamports := by
  by_contra bad
  have zero : account.record.lamports = 0 := by omega
  have size := checkpoint_size e ops id data saved source
  change (e.buffers (e.handles 2).1).val.length = 1768 at size
  rw [bankInput,CPP_BankCache.dead_image account zero] at size
  simp only [List.length_nil] at size
  omega

theorem reader_live {F C : Type} (c : DrvC_Installation.Configuration F C)
    (store : Store) (layout : Layout) (id : S2W_ExtractionBoundary.Program)
    (data : Slice U8) (slot : S2W_ExtractionBoundary.Slot) (account : CPP_BankCache.Account)
    (source : AdapterRw.r1_pool_adapter.owned.stage2_owned (DrvC_Installation.sdk c)
      id ((load store layout).second secondSizes) data slot = ok (.Ok ()))
    (bankInput : (store (layout.handles 6).1).data = CPP_BankCache.image account) :
    0 < account.record.lamports := by
  have marker := Hir_ReaderEntry.marker c store layout id data slot source
  rw [bankInput] at marker
  exact CPP_BankCache.marker_live account marker

#print axioms writer_live
#print axioms reader_live
end AspisR1.CPP_BankSourceLoad
end
