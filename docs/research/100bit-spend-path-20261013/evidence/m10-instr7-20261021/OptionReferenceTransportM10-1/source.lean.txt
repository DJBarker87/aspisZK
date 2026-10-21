import AbstractStageSpecM10

set_option autoImplicit false
namespace AspisR1.OptionReferenceTransportM10

theorem value {A B C : Type} (a : A) (f g : A → Option B) (post : B → Option C)
    (h : f a = g a) :
    ((some a).bind fun x => (f x).bind post) = (g a).bind post :=
  (Option.bind_some a (fun x => (f x).bind post)).trans (congrArg (fun o => o.bind post) h)

#print axioms value
end AspisR1.OptionReferenceTransportM10
