import RPt_BEg_Simulation
import Port4B_LeafCode
set_option autoImplicit false
noncomputable section
namespace AspisR1.BEl_LeafReference
open Aeneas Aeneas.Std Result SdkC_Source

/-- Direct model of the owned Rust reference's argument evaluation: the value
slice is checked before the salt slice. Neither pure check issues a digest. -/
def codeFor (opening : Slice U8) (tag : U8) (vs ve ss se : Usize) : Code Digest :=
  .step (Port4B_LeafCode.readRange opening vs ve) fun value =>
  .step (Port4B_LeafCode.readRange opening ss se) fun salt =>
  .read (Port4B_LeafCode.parts tag value salt) .done

/-- Pure range-check reordering changes neither returned leaf, live common
state nor attempted prefix. Error kinds may differ on short inputs. -/
theorem range_order {S : Type} (call : Parts → S → Result Digest × S)
    (opening : Slice U8) (tag : U8) (vs ve ss se : Usize) (state : S) (before : Log) :
    BEg_Simulation.observation some (BEf_Carrier.run call (codeFor opening tag vs ve ss se) state before) =
      BEg_Simulation.observation some (BEf_Carrier.run call
        (Port4B_LeafCode.codeFor opening tag vs ve ss se) state before) := by
  cases hv : Port4B_LeafCode.readRange opening vs ve <;>
    cases hs : Port4B_LeafCode.readRange opening ss se <;>
    simp only [codeFor,Port4B_LeafCode.codeFor,BEf_Carrier.run,hv,hs,
      BEg_Simulation.observation,BEg_Simulation.value]

def code (kind : Usize) (opening : Slice U8) : Code Digest :=
  if kind=0#usize then codeFor opening 113#u8 0#usize 480#usize 608#usize 640#usize
  else if kind=1#usize then codeFor opening 241#u8 480#usize 608#usize 640#usize 672#usize
  else codeFor opening 114#u8 672#usize 800#usize 800#usize 832#usize

theorem observation {S : Type} (call : Parts → S → Result Digest × S)
    (kind : Usize) (opening : Slice U8) (state : S) (before : Log) :
    BEg_Simulation.observation some (BEf_Carrier.run call (code kind opening) state before) =
      BEg_Simulation.observation some (BEf_Carrier.run call (Port4B_LeafCode.code kind opening) state before) := by
  unfold code Port4B_LeafCode.code
  split
  · exact range_order call opening _ _ _ _ _ state before
  · split <;> exact range_order call opening _ _ _ _ _ state before

#print axioms range_order
#print axioms observation
end AspisR1.BEl_LeafReference
end
