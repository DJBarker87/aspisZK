import NDO_JGx_AdapterSize
import JGx_SdkConstants
set_option autoImplicit false
noncomputable section
namespace AspisR1.JGx_CallerSeed
open Aeneas Aeneas.Std Result DrvC_Installation

/-- The source's literal common-byte constant; no acceptance leaf is selected. -/
def value {C : Type} (c : Configuration FIo_Install.W C) : Configuration FIo_Install.W C :=
  {c with adapter:={c.adapter with op19:=ok 1520#usize}}

theorem common {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    (DrvC_Installation.sdk (JGx_Configuration.value (value c) err)).op19=ok 1520#usize :=
  JGx_AdapterSize.source (value c) err
#print axioms common

theorem statementSize {C : Type} (c : Configuration FIo_Install.W C) (err : C) :
    AdapterRw.aspis_statement.pool_v1.pair_forest_terminal.POOL_V1_PAIR_FOREST_TERMINAL_STATEMENT_BYTES
      (DrvC_Installation.sdk (JGx_Configuration.value (value c) err))=ok 1880#usize :=
  JGx_SdkConstants.statementSize _ (common c err)
#print axioms statementSize
end AspisR1.JGx_CallerSeed
end
