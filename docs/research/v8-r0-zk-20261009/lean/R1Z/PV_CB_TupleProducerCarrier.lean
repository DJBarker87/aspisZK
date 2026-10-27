import R1Z.PV_CB_TupleProducerRoot
import R1Z.PV_CB_ProducerSelected
set_option autoImplicit false
namespace R1Z.PV_CB_TupleProducerCarrier
open Aeneas Aeneas.Std Result
abbrev Bank := ProverRwFull.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceBankV1
abbrev Source := ProverRwFull.aspis_statement.pool_v1.pair_trace.PoolV1PairTraceCellV1
abbrev Limb := ProverRwFull.aspis_statement.pool_v1.pair_trace.PoolV1PairTupleLimbV1
abbrev Tuple := ProverRwFull.aspis_statement.pool_v1.pair_trace.PoolV1PairCopyTupleV1

def bank : PV_CB_TupleProducerOffset.Bank → Bank
  | .Stable => .Stable
  | .Late => .Late

def source (x : PV_CB_TupleProducerOffset.Source) : Source :=
  {bank := bank x.bank,cell := {row := x.cell.row,column := x.cell.column}}

def limb : PV_CB_TupleProducerOffset.Limb → Limb
  | .Zero => .Zero
  | .Cell x offset => .Cell (source x) offset

def limbs (xs : Array PV_CB_TupleProducerOffset.Limb 16#usize) : Array Limb 16#usize :=
  ⟨xs.val.map limb,by rw [List.length_map,xs.property]⟩

def tuple (x : PV_CB_TupleProducerOffset.Tuple) : Tuple :=
  {row := x.row,limbs := limbs x.limbs}

theorem limb_valid (x : PV_CB_TupleProducerOffset.Limb)
    (vx : PV_CB_TupleProducerOffset.ValidLimb x) :
    PV_CB_ProducerLimb.OffsetValid (limb x) := by
  cases x <;> exact vx

theorem limbs_valid (xs : Array PV_CB_TupleProducerOffset.Limb 16#usize)
    (vx : PV_CB_TupleProducerOffset.Valid xs) :
    PV_CB_CanonicalArrays.Valid PV_CB_ProducerLimb.OffsetValid (limbs xs) := by
  intro out member
  change out ∈ xs.val.map limb at member
  obtain ⟨value,hvalue,rfl⟩ := List.mem_map.mp member
  exact limb_valid value (vx value hvalue)

/-- Exact emitted Rust producer, transported into the existing Full caller
    carrier. Every range selector is allowed; no desired source output law. -/
theorem produced [PV_CB_ShippedOp223Tuple.ExternalFuns]
    (row start count : Usize) (tweak_right : Bool) (out : PV_CB_TupleProducerOffset.Tuple)
    (run : PV_CB_ShippedOp223Tuple.pool_v1.pair_trace.tuple_cells row start count tweak_right = ok out) :
    PV_CB_CanonicalArrays.Valid PV_CB_ProducerLimb.OffsetValid (tuple out).limbs :=
  limbs_valid out.limbs (PV_CB_TupleProducerRoot.source row start count tweak_right out run)
#print axioms limb_valid
#print axioms limbs_valid
#print axioms produced
end R1Z.PV_CB_TupleProducerCarrier
