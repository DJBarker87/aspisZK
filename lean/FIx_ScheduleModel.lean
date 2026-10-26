import FIx_InitialVariant
import FIx_HighSum
import FIw_ArrayValue
set_option autoImplicit false
noncomputable section
namespace AspisR1.FIx_ScheduleModel
open Aeneas Aeneas.Std
open FIv_NativeValue (K)
open FIx_HighSumInner (Selectors)
abbrev Openings := FIq_Native.state_only_poseidon.StateOnlyPoseidonOpenings
abbrev Variant := FIq_Native.pool_v1.pair_forest_semantic_terminal.CompiledVariant

def high (s : Selectors) := FIv_NativeArray.value s.high
def low (s : Selectors) := FIv_NativeArray.value s.low

def nodeRanges : Slice (core.ops.range.Range Usize) := Array.to_slice
  (Array.make 2#usize [⟨4#usize,25#usize⟩,⟨33#usize,57#usize⟩])
def nodes (s : Selectors) : K := FIx_HighSumOuter.ranges nodeRanges.val s 0

def variant (v : Variant) (s : Selectors) :=
  R0P.scheduleVariantSelectors (FIw_CoefficientTransport.variant v) (high s 27) (high s 28) (high s 29)

def firstCommon (s : Selectors) := ((high s 0+high s 1)+high s 25)+high s 30

def full (v : Variant) (s : Selectors) := low s 0*((firstCommon s+(variant v s).1)+(variant v s).2.1)
def fullRate (v : Variant) (s : Selectors) := full v s+low s 0*nodes s

def noteFirst (v : Variant) (s : Selectors) := (high s 1+high s 30)+(variant v s).1

def domain (v : Variant) (s : Selectors) :=
  (high s 0*(1095958529 : K)+noteFirst v s*(1095958531 : K))+high s 25*(1095958530 : K)
def length (v : Variant) (s : Selectors) :=
  (high s 0*(8 : K)+noteFirst v s*(18 : K))+high s 25*(16 : K)

def initialRaw (v : Variant) (s : Selectors) (o : Openings) : Fin (16#usize).val → K :=
  fun i=>(if i.val<8 then fullRate v s else full v s)*FIv_NativeArray.value o.z i.val

def initial (v : Variant) (s : Selectors) (o : Openings) : Fin (16#usize).val → K :=
  Function.update (Function.update (initialRaw v s o) ⟨8,by decide⟩
    (initialRaw v s o ⟨8,by decide⟩-low s 0*domain v s)) ⟨9,by decide⟩
    (initialRaw v s o ⟨9,by decide⟩-low s 0*length v s)

def chunkEight (v : Variant) (s : Selectors) :=
  ((((((high s 0+high s 1)+high s 2)+high s 25)+high s 26)+high s 30)+high s 31)+(variant v s).2.2.1
def chunkTwo (v : Variant) (s : Selectors) := (high s 3+high s 32)+(variant v s).2.2.2

def absorption (v : Variant) (s : Selectors) (o : Openings) : Fin (16#usize).val → K :=
  fun i=>low s 12*FIx_Absorption.blocks (variant v s).2.1 (chunkTwo v s)
    (chunkEight v s) (nodes s) i.val*FIv_NativeArray.value o.z i.val
end AspisR1.FIx_ScheduleModel
end
