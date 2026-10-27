import JGa_LinkShape
set_option autoImplicit false
namespace AspisR1.JGa_LinkChunk02
open Aeneas Aeneas.Std FIq_Native
open pool_v1.pair_forest_copy_terminal
open JGa_LinkShape (Good Endpoint)
def values : List CompiledPoolV1PairForestLink := [
{
      tag := 1124073506#u32,
      weight_kind := 3#u8,
      weight_level := 5#u8,
      producer := { row := 619#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 636#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073507#u32,
      weight_kind := 4#u8,
      weight_level := 5#u8,
      producer := { row := 619#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 624#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073508#u32,
      weight_kind := 3#u8,
      weight_level := 6#u8,
      producer := { row := 635#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 652#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073509#u32,
      weight_kind := 4#u8,
      weight_level := 6#u8,
      producer := { row := 635#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 640#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073510#u32,
      weight_kind := 3#u8,
      weight_level := 7#u8,
      producer := { row := 651#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 668#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073511#u32,
      weight_kind := 4#u8,
      weight_level := 7#u8,
      producer := { row := 651#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 656#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073512#u32,
      weight_kind := 3#u8,
      weight_level := 8#u8,
      producer := { row := 667#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 684#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073513#u32,
      weight_kind := 4#u8,
      weight_level := 8#u8,
      producer := { row := 667#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 672#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073514#u32,
      weight_kind := 3#u8,
      weight_level := 9#u8,
      producer := { row := 683#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 700#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073515#u32,
      weight_kind := 4#u8,
      weight_level := 9#u8,
      producer := { row := 683#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 688#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073516#u32,
      weight_kind := 3#u8,
      weight_level := 10#u8,
      producer := { row := 699#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 716#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073517#u32,
      weight_kind := 4#u8,
      weight_level := 10#u8,
      producer := { row := 699#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 704#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073518#u32,
      weight_kind := 3#u8,
      weight_level := 11#u8,
      producer := { row := 715#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 732#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073519#u32,
      weight_kind := 4#u8,
      weight_level := 11#u8,
      producer := { row := 715#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 720#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073520#u32,
      weight_kind := 3#u8,
      weight_level := 12#u8,
      producer := { row := 731#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 748#u16, slot := 0#u8, pattern := 1#u8 }
    },
{
      tag := 1124073521#u32,
      weight_kind := 4#u8,
      weight_level := 12#u8,
      producer := { row := 731#u16, slot := 1#u8, pattern := 1#u8 },
      consumer := { row := 736#u16, slot := 0#u8, pattern := 10#u8 }
    },
{
      tag := 1124073522#u32,
      weight_kind := 3#u8,
      weight_level := 13#u8,
      producer := { row := 747#u16, slot := 0#u8, pattern := 1#u8 },
      consumer := { row := 764#u16, slot := 0#u8, pattern := 1#u8 }
    }]
theorem all : ∀ l∈values,Good l := by
  simp only [values,List.forall_mem_cons,Good,Endpoint]
  repeat' constructor
  all_goals first | scalar_tac | simp
#print axioms all
end AspisR1.JGa_LinkChunk02
