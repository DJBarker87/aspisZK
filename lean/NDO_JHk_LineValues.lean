import NDO_JHk_Line00
import NDO_JHk_Line01
import NDO_JHk_Line02
import NDO_JHk_Line03
import NDO_JHk_Line04
import NDO_JHk_Line05
import NDO_JHk_Line06
import NDO_JHk_Line07
import NDO_JHk_Line08
import NDO_JHk_Line09
import NDO_JHk_LineRead
set_option autoImplicit false
namespace AspisR1.JHk_LineValues
def value (i : Fin 10) : AspisWideTower.WideExact := match i.val with
  | 0 => JHk_Line00.value
  | 1 => JHk_Line01.value
  | 2 => JHk_Line02.value
  | 3 => JHk_Line03.value
  | 4 => JHk_Line04.value
  | 5 => JHk_Line05.value
  | 6 => JHk_Line06.value
  | 7 => JHk_Line07.value
  | 8 => JHk_Line08.value
  | _ => JHk_Line09.value
theorem source (i : Fin 10) :
    CheckpointBytes5Output.ofE (JHk_LineRead.value i)=value i := by
  fin_cases i
  · exact JHk_Line00.source
  · exact JHk_Line01.source
  · exact JHk_Line02.source
  · exact JHk_Line03.source
  · exact JHk_Line04.source
  · exact JHk_Line05.source
  · exact JHk_Line06.source
  · exact JHk_Line07.source
  · exact JHk_Line08.source
  · exact JHk_Line09.source
#print axioms source
end AspisR1.JHk_LineValues
