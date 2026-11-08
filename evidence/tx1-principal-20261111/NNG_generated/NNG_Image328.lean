import NNG_Producer328
set_option autoImplicit false
noncomputable section
namespace AspisR1.NNG_Image328
open Aeneas Aeneas.Std Result

theorem roundtrip (a : NNG_Native328.Args) (bound : a.k.val≤UScalar.cMax .Usize) :
 NNG_Native328.input (NNG_Native328.args a)=a := by
 cases a with
 | mk pub publicBytes proof k=>
  unfold NNG_Native328.input NNG_Native328.args
  rw [NNG_Carriers328.from_to,LIBC_Bytes.from_native,LIBC_Bytes.from_native]
  have scalar : LIBC_Usize.raw k.val=k := LIBC_Usize.from_native k bound
  rw [scalar]
#print axioms roundtrip

theorem source (a : NNG_Native328.Args) (env : RSL.Env) (bound : a.k.val≤UScalar.cMax .Usize) :
 NNG_Producer328.producer (NNG_Native328.args a) env=
 NNG_Observed136.observation NNG_Carriers328.port (NNG_Tree328.events env) (NNG_Tree328.tree a env) := by
 rw [NNG_Producer328.tree,roundtrip a bound]
#print axioms source
end AspisR1.NNG_Image328
