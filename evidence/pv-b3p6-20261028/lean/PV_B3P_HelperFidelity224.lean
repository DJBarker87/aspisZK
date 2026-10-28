import PV_B3P_HelperComplete224
namespace PV_B3P_HelperFidelity224
open Aeneas Aeneas.Std PV_B3P_224
set_option autoImplicit false
-- Sparse preflight: 1023 inactive rows skip every arithmetic call; the only
-- active endpoint has chi-value=2. The symbolic full-loop theorem is checked
-- before this compiled finite evaluation. No kernel certificate is inferred.
def q (n : U32) : aspis_core.field.QM31 := ⟨⟨n,0#u32⟩,⟨0#u32,0#u32⟩⟩
def empty : aspis_statement.logup.CopyLogUpRow :=
  {producer_values := Array.repeat 2#usize (q 0#u32)
   producer_weights := Array.repeat 2#usize 0#u32
   consumer_values := Array.repeat 2#usize (q 0#u32)
   consumer_weights := Array.repeat 2#usize 0#u32}
def active : aspis_statement.logup.CopyLogUpRow :=
  {empty with producer_values := empty.producer_values.set 0#usize (q 1#u32)
              producer_weights := empty.producer_weights.set 0#usize 1#u32}
def rows : Array aspis_statement.logup.CopyLogUpRow 1024#usize :=
  (Array.repeat 1024#usize empty).set 1023#usize active
def words (x : aspis_core.field.QM31) : List Nat := [x.c0.a.val,x.c0.b.val,x.c1.a.val,x.c1.b.val]
#eval match reference224.from_rows rows (q 3#u32) with
  | .ok (.Ok out) => IO.println s!"D188-helper224-values={out.val.map words}"
  | .ok (.Err _) => IO.println "D188-helper224-rejected"
  | .fail _ => IO.println "D188-helper224-failed"
  | .div => IO.println "D188-helper224-diverged"
end PV_B3P_HelperFidelity224
