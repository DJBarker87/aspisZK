import NGX_SamplerJoin
import NGX_SampleTrace
set_option autoImplicit false
open Aeneas Aeneas.Std Result AspisR1PublicPreparation
open AspisR1PublicPreparation.PreparedHashCode
namespace AspisR1.NGX_RunBind

def appendResult {A B : Type} (log : Log) (reply : Result A) (next : A→Code B) : Log×Result B :=
 match reply with
 | .ok value => let tail:=run (next value);(log++tail.1,tail.2)
 | .fail e => (log,.fail e)
 | .div => (log,.div)

theorem bind_run {A B : Type} (code : Code A) (next : A→Code B) :
 run (code >>= next)=appendResult (run code).1 (run code).2 next := by
 induction code with
 | done a => rfl
 | step reply cont ih =>
   cases reply with
   | ok value => exact ih value
   | fail e=>rfl
   | div=>rfl
 | digest D hash parts cont ih =>
   change run (Code.digest D hash parts (fun x=>AspisR1PublicPreparation.PreparedHashCode.bind (cont x) next))=_
   cases h : D.digest hash parts with
   | fail e=>simp only [run,h,appendResult]
   | div=>simp only [run,h,appendResult]
   | ok value=>
     simp only [run,h,ih]
     cases r : (run (cont value)).2 <;> simp only [appendResult,r,List.cons_append]
#print axioms bind_run
end AspisR1.NGX_RunBind
