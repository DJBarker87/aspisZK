"""Private compiler experiment; source lowering, never generated-output repair."""
from pathlib import Path
D=Path('/home/dombarker/project-offloads/codex-cx-prover-rw-20261023/native-drop-abi/backend/base/src')
p=D/'PrePasses.ml';s=p.read_text()
needle='let apply_passes (crate : crate) : crate ='
assert s.count(needle)==1
addition='''(* ProverRwNativeDropABI: route the exact swap primitive through ordinary
   move/borrow translation. No callback, cleanup or destructor is evaluated
   by this pass; unsupported instantiations fail before any accepted output. *)
let lower_nested_borrow_swap (crate : crate) (f : fun_decl) : fun_decl =
  let is_swap (d : fun_decl) =
    d.item_meta.name = to_name ["core"; "mem"; "swap"] &&
    d.item_meta.lang_item = Some "mem_swap" in
  let nested_leaf = function TRef (_, TLiteral _, RMut) -> true | _ -> false in
  let supported ty = match ty with
    | TRef _ -> nested_leaf ty
    | TAdt {id=TAdtId id; generics=g} ->
        (match TypeDeclId.Map.find_opt id crate.type_decls, g.types with
         | Some d, [t] when d.item_meta.lang_item = Some "Option" -> nested_leaf t
         | _ -> false)
    | _ -> false in
  match f.body with
  | StructuredBody body ->
      let added = ref [] in
      let _, gen = LocalId.mk_stateful_generator_starting_at_id
        (LocalId.of_int (List.length body.locals.locals)) in
      let fresh ty =
        let id = gen () in
        added := {index=id; local_ty=ty; name=None; span=body.span} :: !added;
        {kind=PlaceLocal id; ty} in
      let local_id (p : place) = match p.kind with
        | PlaceLocal id -> id | _ -> assert false in
      let lower (st : statement) =
        let mk kind = {st with kind; statement_id=StatementId.zero} in
        match st.kind with
        | Call ({func=FnOpRegular {kind=FunId (FRegular id); generics};
                 args; dest}, _unwind) ->
          (match FunDeclId.Map.find_opt id crate.fun_decls with
           | Some d when is_swap d ->
             (match generics.types with
              | [t] when supported t ->
                let sg = d.signature in
                let valid_sig = match sg.inputs with
                  | [TRef (_, (TVar (Free _) as t0), RMut);
                     TRef (_, t1, RMut)] -> t0=t1
                  | _ -> false in
                [%cassert] st.span
                  (valid_sig && not sg.is_unsafe && sg.abi=AbiRust &&
                   not sg.is_variadic && sg.output=mk_unit_ty &&
                   List.length d.generics.regions=2 &&
                   List.length d.generics.types=1 &&
                   d.generics.const_generics=[] &&
                   d.generics.regions_outlive=[] &&
                   d.generics.types_outlive=[] &&
                   d.generics.trait_type_constraints=[] &&
                   List.length generics.regions=2 &&
                   generics.const_generics=[] && dest.ty=mk_unit_ty)
                  "ProverRwNativeDropABI: unsupported swap signature";
                (match args with
                 | [Move ({kind=PlaceLocal _; ty=TRef (_, t0, RMut)} as a);
                    Move ({kind=PlaceLocal _; ty=TRef (_, t1, RMut)} as b)]
                    when t0=t1 && t0=ty_erase_regions t ->
                   let left=fresh a.ty in
                   let right=fresh b.ty in
                   let tmp=fresh t0 in
                   let deref p = {kind=PlaceProjection (p,Deref); ty=t0} in
                   let assign p v = mk (Assign (p,Use (v,NoRetag))) in
                   (* Intrinsic swap is non-unwinding; these moves execute no
                      code. Other calls retain their original unwind blocks. *)
                   [assign left (Move a); assign right (Move b);
                    assign tmp (Move (deref left));
                    assign (deref left) (Move (deref right));
                    assign (deref right) (Move tmp);
                    assign dest (Constant mk_unit_const);
                    mk (StorageDead (local_id left));
                    mk (StorageDead (local_id right));
                    mk (StorageDead (local_id tmp))]
                 | _ -> [%craise] st.span "ProverRwNativeDropABI: unsupported swap operands")
              | _ ->
                (* Leave reference-free builtins unchanged. Any nested shape
                   not explicitly supported is rejected rather than pair-mapped. *)
                let has_ref = ref false in
                let visitor = object inherit [_] iter_ty as super
                  method! visit_ty env ty =
                    (match ty with TRef _ -> has_ref:=true | _ -> ());
                    super#visit_ty env ty end in
                List.iter (visitor#visit_ty ()) generics.types;
                if !has_ref then [%craise] st.span "ProverRwNativeDropABI: unsupported nested swap type"
                else [st])
           | _ -> [st])
        | _ -> [st] in
      let rewritten = map_statement lower body.body in
      {f with body=StructuredBody {body with body=rewritten;
        locals={body.locals with locals=body.locals.locals @ List.rev !added}}}
  | _ -> f

'''
s=s.replace(needle,addition+needle).replace('("lower_precise_local_drops", lower_precise_local_drops);','("lower_precise_local_drops", lower_precise_local_drops);\n      ("lower_nested_borrow_swap", lower_nested_borrow_swap);')
p.write_text(s)
p=D/'extract/Extract.ml';s=p.read_text()
a='''  let _ = inside in
  (* Remark: we don't use the [inside] parameter because we extract matches in
     a conservative manner: we always make sure they are parenthesized/delimited
     with keywords such as [end] *)'''
b='''  (* Lean uses indentation rather than end, so argument-position switches
     require explicit parentheses. This also isolates branch result typing. *)
  let parenthesize = backend () = Lean && inside in
  if parenthesize then F.pp_print_string fmt "(";'''
assert s.count(a)==1;s=s.replace(a,b)
a='''  F.pp_close_box fmt ()

and extract_meta'''
b='''  F.pp_close_box fmt ();
  if parenthesize then F.pp_print_string fmt ")"

and extract_meta'''
assert s.count(a)==1;s=s.replace(a,b);p.write_text(s)
