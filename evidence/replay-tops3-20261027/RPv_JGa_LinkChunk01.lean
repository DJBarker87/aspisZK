import RPv_JGa_LinkShape
set_option autoImplicit false
namespace AspisR1.JGa_LinkChunk01
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open JGa_LinkShape (Good Endpoint)
def values : List CompiledPoolV1PairForestLink := [
{
      tag := 1124073489#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 1014#u16, slot := 0#u8, pattern := 9#u8 },
      consumer := { row := 1015#u16, slot := 1#u8, pattern := 6#u8 }
    },
{
      tag := 1124073490#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 64#u16, slot := 0#u8, pattern := 10#u8 },
      consumer := { row := 1017#u16, slot := 0#u8, pattern := 11#u8 }
    },
{
      tag := 1124073491#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 913#u16, slot := 0#u8, pattern := 6#u8 },
      consumer := { row := 1017#u16, slot := 1#u8, pattern := 7#u8 }
    },
{
      tag := 1124073492#u32,
      weight_kind := 1#u8,
      weight_level := 0#u8,
      producer := { row := 523#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 1018#u16, slot := 0#u8, pattern := 11#u8 }
    },
{
      tag := 1124073493#u32,
      weight_kind := 1#u8,
      weight_level := 0#u8,
      producer := { row := 475#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 540#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073494#u32,
      weight_kind := 2#u8,
      weight_level := 0#u8,
      producer := { row := 523#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 540#u16, slot := 1#u8, pattern := 1#u8 }
    },
{
      tag := 1124073495#u32,
      weight_kind := 0#u8,
      weight_level := 0#u8,
      producer := { row := 1018#u16, slot := 0#u8, pattern := 11#u8 },
      consumer := { row := 528#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073496#u32,
      weight_kind := 3#u8,
      weight_level := 0#u8,
      producer := { row := 539#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 556#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073497#u32,
      weight_kind := 4#u8,
      weight_level := 0#u8,
      producer := { row := 539#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 544#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073498#u32,
      weight_kind := 3#u8,
      weight_level := 1#u8,
      producer := { row := 555#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 572#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073499#u32,
      weight_kind := 4#u8,
      weight_level := 1#u8,
      producer := { row := 555#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 560#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073500#u32,
      weight_kind := 3#u8,
      weight_level := 2#u8,
      producer := { row := 571#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 588#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073501#u32,
      weight_kind := 4#u8,
      weight_level := 2#u8,
      producer := { row := 571#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 576#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073502#u32,
      weight_kind := 3#u8,
      weight_level := 3#u8,
      producer := { row := 587#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 604#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073503#u32,
      weight_kind := 4#u8,
      weight_level := 3#u8,
      producer := { row := 587#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 592#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073504#u32,
      weight_kind := 3#u8,
      weight_level := 4#u8,
      producer := { row := 603#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 620#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073505#u32,
      weight_kind := 4#u8,
      weight_level := 4#u8,
      producer := { row := 603#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 608#u16, slot := 0#u8, pattern := 10#u8 }
    }]
theorem all : ∀ l∈values,Good l := by
  simp only [values,List.forall_mem_cons,Good,Endpoint]
  repeat' constructor
  all_goals first | scalar_tac | simp
#print axioms all
end AspisR1.JGa_LinkChunk01
