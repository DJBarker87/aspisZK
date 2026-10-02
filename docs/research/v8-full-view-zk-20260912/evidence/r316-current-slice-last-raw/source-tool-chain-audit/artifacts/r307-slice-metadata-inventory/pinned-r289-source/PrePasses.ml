(** This files contains passes we apply on the AST *before* calling the
    (concrete/symbolic) interpreter on it *)

open Types
open TypesUtils
open Expressions
open ExpressionsUtils
open LlbcAst
open Utils
open LlbcAstUtils
open Errors

let log = Logging.pre_passes_log

let statement_to_string (crate : crate) =
  let fmt_env = Print.crate_to_fmt_env crate in
  Print.statement_to_string fmt_env "" "  "

let call_to_string (crate : crate) =
  let fmt_env = Print.crate_to_fmt_env crate in
  Print.call_to_string fmt_env "  "

let fun_decl_ref_to_string (crate : crate) =
  let fmt_env = Print.crate_to_fmt_env crate in
  Print.fun_decl_ref_to_string fmt_env

let generic_args_to_string (crate : crate) (generics : generic_args) =
  let fmt_env = Print.crate_to_fmt_env crate in
  let generics, traits = Print.generic_args_to_strings fmt_env generics in
  "<" ^ String.concat ", " (generics @ traits) ^ ">"

let generic_params_to_string (crate : crate) (generics : generic_params) =
  let fmt_env = Print.crate_to_fmt_env crate in
  let generics, traits = Print.generic_params_to_strings fmt_env generics in
  "<" ^ String.concat ", " (generics @ traits) ^ ">"

(** Erase the useless body regions.

    We erase the body regions which appear in:
    - locals
    - places

    We only keep those used in function calls. *)
let erase_body_regions (crate : crate) (f : fun_decl) : fun_decl =
  let f0 = f in

  let erase_visitor =
    object
      inherit [_] map_statement

      method! visit_fn_operand _ x =
        (* Do not erase the use of body regions inside function operands *)
        x

      method! visit_RBody _ _ = RErased
      method! visit_RVar _ _ = RErased
      method! visit_RStatic _ = RErased
    end
  in

  (* Map  *)
  let body =
    match f.body with
    | StructuredBody body ->
        let body =
          {
            body with
            locals =
              {
                body.locals with
                locals =
                  List.map Contexts.local_erase_regions body.locals.locals;
              };
          }
        in
        StructuredBody
          { body with body = erase_visitor#visit_block 0 body.body }
    | other -> other
  in

  let f : fun_decl = { f with body } in
  [%ldebug
    let env = Print.crate_to_fmt_env crate in
    "Before/after [erase_body_regions]:\n"
    ^ Print.fun_decl_to_string env "" "  " f0
    ^ "\n\n"
    ^ Print.fun_decl_to_string env "" "  " f];
  f

(** Eliminate the metadata-only raw pointers which rustc introduces while
    lowering slice patterns.

    For a match such as [(indices, values) = ([0, 1], [left, right])], rustc
    currently emits the following shape (irrelevant temporaries omitted):

    {[
      raw = raw_pointer_to (deref slice_ref, copy slice_ref.metadata);
      len = copy raw.metadata
    ]}

    The raw pointer is an implementation detail of the length check: its data
    address is never observed. In that exact case this pass changes the raw
    pointer temporary into a [usize] temporary, initializes it by calling the
    safe slice [len] operation at the original statement, and rewrites the later
    metadata read to read that temporary. Keeping the initialization at the
    original statement is important: [slice_ref] may be reassigned before the
    metadata is used. Calling [len] also avoids treating pointer metadata as an
    independent, unconstrained value in the functional translation.

    This is deliberately not general raw-pointer support. A candidate is
    rewritten only when:
    - it points to a slice through a shared safe Rust reference;
    - the metadata used to construct it is the metadata of that same reference;
    - it has exactly one use, which is a read of its [usize] metadata; and
    - it has exactly one definition.

    Any dereference, cast, comparison, address observation, call escape,
    reassignment, or second use leaves the raw pointer untouched. The normal
    interpreter will then reject it as unsupported. Requiring a single read also
    ensures that the transformed [usize] temporary has the same linear
    definition/use shape as the original raw-pointer temporary. *)
type metadata_only_slice_raw_pointer = {
  definition : statement_id;
  reference : place;
  elem_ty : ty;
}

let eliminate_metadata_only_slice_raw_pointers (crate : crate) (f : fun_decl) :
    fun_decl =
  let metadata_definition (st : statement) :
      (local_id * metadata_only_slice_raw_pointer) option =
    match st.kind with
    | Assign
        ( {
            kind = PlaceLocal local;
            ty = TRawPtr (TSlice raw_elem_ty, raw_kind);
          },
          RawPtr
            ( { kind = PlaceProjection (reference, Deref); ty = TSlice elem_ty },
              ptr_kind,
              (Copy metadata_place | Move metadata_place) ) )
      when raw_elem_ty = elem_ty && raw_kind = ptr_kind
           && metadata_place.ty = mk_usize_ty -> (
        match (reference.ty, metadata_place.kind) with
        | ( TRef (_, TSlice reference_elem_ty, _),
            PlaceProjection (metadata_reference, PtrMetadata) )
          when reference_elem_ty = elem_ty && metadata_reference = reference
          -> (
            match reference.ty with
            | TRef (_, _, RShared) ->
                Some
                  (local, { definition = st.statement_id; reference; elem_ty })
            | _ -> None)
        | _ -> None)
    | _ -> None
  in
  (* The generated call deliberately targets Charon's existing slice-length
     language item.  If it is absent or ambiguous we decline the rewrite. *)
  let slice_len_ids =
    FunDeclId.Map.fold
      (fun id (decl : fun_decl) ids ->
        if decl.item_meta.lang_item = Some "slice_len_fn" then id :: ids
        else ids)
      crate.fun_decls []
  in
  match slice_len_ids with
  | [ slice_len_id ] -> (
      let slice_len_call (st : statement) (dest : place) (reference : place)
          (elem_ty : ty) : statement_kind =
        let generics =
          TypesUtils.mk_generic_args [ RErased ] [ elem_ty ] [] []
        in
        let call =
          {
            func =
              FnOpRegular { kind = FunId (FRegular slice_len_id); generics };
            args = [ Copy reference ];
            dest;
          }
        in
        Call (call, { span = st.span; statements = [] })
      in
      (* Some slice patterns lower directly to a metadata read on a shared safe
         slice reference, without an intermediate raw pointer.  This is the
         same length operation and can be rewritten without any use analysis. *)
      let direct_metadata_rewriter =
        object
          inherit [_] map_statement as super

          method! visit_statement env st =
            match st.kind with
            | Assign
                (dest, Use ((Copy metadata_place | Move metadata_place), _retag))
              when dest.ty = mk_usize_ty && metadata_place.ty = mk_usize_ty -> (
                match metadata_place.kind with
                | PlaceProjection
                    ( ({ ty = TRef (_, TSlice elem_ty, RShared); _ } as reference),
                      PtrMetadata ) ->
                    { st with kind = slice_len_call st dest reference elem_ty }
                | _ -> super#visit_statement env st)
            | _ -> super#visit_statement env st
        end
      in
      let f =
        match f.body with
        | StructuredBody body ->
            let body =
              {
                body with
                body = direct_metadata_rewriter#visit_block () body.body;
              }
            in
            { f with body = StructuredBody body }
        | _ -> f
      in
      match f.body with
      | StructuredBody body ->
          (* First collect definitions.  A local with more than one definition is
         intentionally not a candidate. *)
          let definitions = ref LocalId.Map.empty in
          let collector =
            object
              inherit [_] iter_statement as super

              method! visit_statement env st =
                (match metadata_definition st with
                | None -> ()
                | Some (local, definition) ->
                    definitions :=
                      LocalId.Map.update local
                        (fun previous ->
                          Some
                            (definition
                            ::
                            (match previous with
                            | None -> []
                            | Some xs -> xs)))
                        !definitions);
                super#visit_statement env st
            end
          in
          collector#visit_block () body.body;
          let candidates =
            LocalId.Map.filter_map
              (fun _ definitions ->
                match definitions with
                | [ definition ] -> Some definition
                | _ -> None)
              !definitions
          in
          if LocalId.Map.is_empty candidates then f
          else
            (* Classify every use.  Exact [copy/move raw.metadata] operands are the
           sole permitted use.  Every other place rooted at the raw local is
           forbidden.  Storage markers contain a local id rather than a place
           and are deliberately ignored. *)
            let invalid = ref LocalId.Set.empty in
            let reads = ref LocalId.Map.empty in
            let add_read local =
              reads :=
                LocalId.Map.update local
                  (fun count -> Some (1 + Option.value ~default:0 count))
                  !reads
            in
            let rec root_local (p : place) : local_id option =
              match p.kind with
              | PlaceLocal local -> Some local
              | PlaceProjection (p, _) -> root_local p
              | PlaceGlobal _ -> None
            in
            let metadata_read (p : place) : local_id option =
              match p.kind with
              | PlaceProjection
                  ( { kind = PlaceLocal local; ty = TRawPtr (TSlice _, _) },
                    PtrMetadata )
                when p.ty = mk_usize_ty && LocalId.Map.mem local candidates ->
                  Some local
              | _ -> None
            in
            let classifier =
              object (self)
                inherit [_] iter_statement as super

                method! visit_statement env st =
                  match metadata_definition st with
                  | Some (local, definition)
                    when LocalId.Map.mem local candidates
                         && definition.definition = st.statement_id ->
                      (* Visit the source place and metadata operand, but not the
                     defining destination local. *)
                      self#visit_rvalue env
                        (match st.kind with
                        | Assign (_, rv) -> rv
                        | _ -> assert false)
                  | _ -> super#visit_statement env st

                method! visit_operand env op =
                  match op with
                  | Copy p | Move p -> (
                      match metadata_read p with
                      | Some local -> add_read local
                      | None -> super#visit_operand env op)
                  | Constant _ -> super#visit_operand env op

                method! visit_place env p =
                  match root_local p with
                  | Some local when LocalId.Map.mem local candidates ->
                      invalid := LocalId.Set.add local !invalid
                  | _ -> super#visit_place env p

                method! visit_local_id _ _ = ()
              end
            in
            classifier#visit_block () body.body;
            let candidates =
              LocalId.Map.filter
                (fun local _ ->
                  (not (LocalId.Set.mem local !invalid))
                  && LocalId.Map.find_opt local !reads = Some 1)
                candidates
            in
            if LocalId.Map.is_empty candidates then f
            else
              let rewriter =
                object
                  inherit [_] map_statement as super

                  method! visit_statement env st =
                    match metadata_definition st with
                    | Some (local, definition) -> (
                        match LocalId.Map.find_opt local candidates with
                        | Some candidate
                          when candidate.definition = definition.definition ->
                            {
                              st with
                              kind =
                                slice_len_call st
                                  { kind = PlaceLocal local; ty = mk_usize_ty }
                                  candidate.reference candidate.elem_ty;
                            }
                        | _ -> super#visit_statement env st)
                    | None -> super#visit_statement env st

                  method! visit_operand env op =
                    match op with
                    | (Copy p | Move p) as original -> (
                        match metadata_read p with
                        | Some local -> (
                            match LocalId.Map.find_opt local candidates with
                            | Some _ -> (
                                let p =
                                  { kind = PlaceLocal local; ty = mk_usize_ty }
                                in
                                match original with
                                | Copy _ -> Copy p
                                | Move _ -> Move p
                                | _ -> assert false)
                            | None -> super#visit_operand env op)
                        | None -> super#visit_operand env op)
                    | Constant _ -> super#visit_operand env op
                end
              in
              let body_body = rewriter#visit_block () body.body in
              let locals =
                {
                  body.locals with
                  locals =
                    List.map
                      (fun (local : local) ->
                        if LocalId.Map.mem local.index candidates then
                          { local with local_ty = mk_usize_ty }
                        else local)
                      body.locals.locals;
                }
              in
              let f =
                {
                  f with
                  body = StructuredBody { body with body = body_body; locals };
                }
              in
              [%ldebug
                let env = Print.crate_to_fmt_env crate in
                "After eliminating metadata-only slice raw pointers:\n"
                ^ Print.fun_decl_to_string env "" " " f];
              f
      | _ -> f)
  | _ -> f

(** Replace the occurrences of [core::intrinsics::unreachable] with
    [Abort UndefinedBehavior]. This helps with the analyzes and the symbolic
    evaluation (in particular, we stop the evaluation when encountering an
    [Abort] - this can help us avoid merging control-flow after a match for
    instance *)
let remove_unreachable (crate : crate) (f : fun_decl) : fun_decl =
  let impl_pat = NameMatcher.parse_pattern "core::intrinsics::unreachable" in
  let mctx = NameMatcher.ctx_from_crate crate in
  let match_name =
    NameMatcher.match_name mctx
      {
        map_vars_to_vars = true;
        match_with_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
      }
  in

  let is_unreachable (st : statement) : bool =
    match st.kind with
    | Call (call, _) -> (
        match call.func with
        | FnOpRegular { kind; _ } -> (
            match kind with
            | FunId (FRegular fid) -> (
                match FunDeclId.Map.find_opt fid crate.fun_decls with
                | Some fun_decl -> match_name impl_pat fun_decl.item_meta.name
                | None -> false)
            | _ -> false)
        | FnOpDynamic _ -> false)
    | _ -> false
  in
  let rec update (stl : statement list) : statement list =
    match stl with
    | [] -> []
    | st :: stl ->
        if is_unreachable st then [ { st with kind = Abort UndefinedBehavior } ]
        else st :: update stl
  in
  let visitor =
    object
      inherit [_] map_statement_base as super

      method! visit_block env b =
        let b = { b with statements = update b.statements } in
        super#visit_block env b
    end
  in
  match f.body with
  | StructuredBody body ->
      let body = { body with body = visitor#visit_block () body.body } in
      { f with body = StructuredBody body }
  | _ -> f

(** The Rust compiler generates a unique implementation of [Default] for arrays
    for every choice of length. For instance, if we write:
    {[
      let a: [u8; 32] = default ();
      let b: [u8; 64] = default ();
      ...
    ]}
    then rustc will introduce two different implementations of [Default]: an
    implementation for [u8; 32] and a different one for [u8; 64].

    For the purpose of the translation, we prefer using a single implementation
    which is generic in the length of the array. This pass thus replaces all the
    implementations of [Default<[T; N]>] with a single implementation.

    Concretely, we spot all the instances of [Default<[T; N]>] where [N] is a
    concrete array. We update the first such implementation so that it becomes
    generic in the length of the array, and replace all the other ones with this
    implementation. We also remove the useless implementations. *)
let update_array_default (crate : crate) : crate =
  let pctx = Print.crate_to_fmt_env crate in
  let impl_pat = NameMatcher.parse_pattern "core::default::Default" in
  let mctx = NameMatcher.ctx_from_crate crate in
  let match_name =
    NameMatcher.match_name mctx
      {
        map_vars_to_vars = true;
        match_with_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
      }
  in

  (* Helper: check whether a trait impl matches the [Default<[T; N]>] pattern,
     and if so return its array length [N]. We ignore the case where the length
     is equal to 0, because in this case rustc uses a different impl which
     doesn't require that the type of the elements also has a default
     implementation. *)
  let matches_default_array (impl : trait_impl) : constant_expr option =
    match TraitDeclId.Map.find_opt impl.impl_trait.id crate.trait_decls with
    | None ->
        (* A deliberately excluded standard-library namespace may leave a
           referenced implementation without its declaration.  It cannot be
           identified as an array Default implementation, so ignore it. *)
        None
    | Some trait_decl ->
        if not (match_name impl_pat trait_decl.item_meta.name) then None
        else
          match impl.impl_trait.generics with
          | {
           regions = [];
           types =
             [
               TArray
                 ( TVar (Free _),
                   ({ kind = CLiteral (VScalar (UnsignedScalar (Usize, nv))); _ } as
                    n) );
             ];
           const_generics = [];
           trait_refs = _;
          }
            when Z.to_int nv != 0 -> Some n
          | _ -> None
  in

  (* First pass: collect all the trait impls matching [Default<[T; N]>] and
     their default methods, together with the array length [N]. *)
  let impls = ref TraitImplId.Map.empty in
  let methods = ref FunDeclId.Map.empty in
  TraitImplId.Map.iter
    (fun _ (impl : trait_impl) ->
      match matches_default_array impl with
      | None -> ()
      | Some n ->
          [%ldebug
            "found a matching impl.\n - decl_generics: "
            ^ Print.generic_args_to_string pctx impl.impl_trait.generics];
          impls := TraitImplId.Map.add impl.def_id n !impls;
          [%sanity_check_opt_span] None
            (TraitMethodId.Map.cardinal impl.methods = 1);
          let meth = List.hd (TraitMethodId.Map.values impl.methods) in
          [%sanity_check_opt_span] None
            (meth.binder_params = empty_generic_params);
          let method_id = meth.binder_value.id in
          methods := FunDeclId.Map.add method_id n !methods)
    crate.trait_impls;
  let impls = !impls in
  let methods = !methods in

  (* If we didn't find any matching impl, there is nothing to do. *)
  if TraitImplId.Map.is_empty impls then crate
  else
    (* Pick the impl into which we will merge all the others.  Prefer the smallest id
       among the impls whose def_id appears in the declarations to extract, so that the
       merged impl is actually emitted. If none of the matching impls is in the
       declarations, fall back to the smallest id: the merging is still useful so that
       builtin name mappings (which match the generic pattern [@T; @N]) can resolve
       references at use sites. *)
    let decl_ids = ref TraitImplId.Set.empty in
    let collect_visitor =
      object
        inherit [_] iter_crate

        method! visit_trait_impl_id _ id =
          TraitImplId.Set.add_in_place id decl_ids
      end
    in
    List.iter (collect_visitor#visit_declaration_group ()) crate.declarations;
    let impls_in_decls =
      TraitImplId.Map.filter
        (fun id _ -> TraitImplId.Set.mem id !decl_ids)
        impls
    in
    let merged_impl_id, _ =
      if TraitImplId.Map.is_empty impls_in_decls then
        TraitImplId.Map.min_binding impls
      else TraitImplId.Map.min_binding impls_in_decls
    in
    let merged_impl =
      [%silent_unwrap_opt_span] None
        (TraitImplId.Map.find_opt merged_impl_id crate.trait_impls)
    in
    let merged_method =
      let meth = List.hd (TraitMethodId.Map.values merged_impl.methods) in
      meth.binder_value.id
    in

    (* Update the chosen merged_impl in place: make it generic in the
       array length. *)
    let merged_impl =
      let cg_id = ConstGenericVarId.zero in
      let cg : Types.constant_expr =
        { kind = CVar (Free cg_id); ty = TypesUtils.mk_usize_ty }
      in
      let elem_ty =
        match merged_impl.impl_trait.generics.types with
        | [ TArray ((TVar (Free _) as elem_ty), _) ] -> elem_ty
        | _ -> [%internal_error] merged_impl.item_meta.span
      in
      let generics =
        {
          merged_impl.impl_trait.generics with
          types = [ TArray (elem_ty, cg) ];
        }
      in
      let impl_trait = { merged_impl.impl_trait with generics } in
      let params =
        {
          merged_impl.generics with
          const_generics =
            [ { index = cg_id; name = "N"; ty = TypesUtils.mk_usize_ty } ];
        }
      in
      { merged_impl with impl_trait; generics = params }
    in

    (* Replace [merged_impl] in [crate.trait_impls] and filter out the
       other matching impls. *)
    let crate =
      {
        crate with
        trait_impls =
          TraitImplId.Map.filter_map
            (fun id impl ->
              if id = merged_impl.def_id then Some merged_impl
              else if TraitImplId.Map.mem id impls then None
              else Some impl)
            crate.trait_impls;
      }
    in

    (* Filter the functions *)
    let visit_fun id (fdecl : fun_decl) =
      match FunDeclId.Map.find_opt id methods with
      | None -> Some fdecl
      | Some _ ->
          if id = merged_method then (
            (* Update the method *)
            let cg_id = ConstGenericVarId.zero in
            let cg : Types.constant_expr =
              { kind = CVar (Free cg_id); ty = TypesUtils.mk_usize_ty }
            in
            let sg = fdecl.signature in
            [%sanity_check_opt_span] None (sg.inputs = []);
            match sg.output with
            | TArray ((TVar (Free _) as elem_ty), _) ->
                let generics =
                  {
                    fdecl.generics with
                    const_generics =
                      [
                        {
                          index = cg_id;
                          name = "N";
                          ty = TypesUtils.mk_usize_ty;
                        };
                      ];
                  }
                in
                let sg = { sg with output = TArray (elem_ty, cg) } in
                let fdecl = { fdecl with signature = sg; generics } in
                Some fdecl
            | _ -> [%internal_error] fdecl.item_meta.span)
          else (* Filter *)
            None
    in
    let filter_ids_visitor =
      object
        inherit [_] filter_decl_id

        method! visit_trait_impl_id _ id =
          match TraitImplId.Map.find_opt id impls with
          | None -> Some id
          | Some _ -> if id = merged_impl.def_id then Some id else None

        method! visit_fun_decl_id _ id =
          match FunDeclId.Map.find_opt id methods with
          | None -> Some id
          | Some _ -> if id = merged_method then Some id else None
      end
    in
    let crate =
      {
        crate with
        fun_decls = FunDeclId.Map.filter_map visit_fun crate.fun_decls;
        declarations =
          filter_ids_visitor#visit_declaration_groups () crate.declarations;
      }
    in

    (* Update all the definitions in the crate *)
    let visitor =
      object
        inherit [_] map_crate_with_span as super

        method! visit_TraitImpl env impl_ref =
          match TraitImplId.Map.find_opt impl_ref.id impls with
          | None -> super#visit_TraitImpl env impl_ref
          | Some n ->
              super#visit_TraitImpl env
                {
                  id = merged_impl.def_id;
                  generics = { impl_ref.generics with const_generics = [ n ] };
                }

        method! visit_fn_ptr env fn_ptr =
          match fn_ptr.kind with
          | FunId (FRegular fid) -> begin
              match FunDeclId.Map.find_opt fid methods with
              | None -> super#visit_fn_ptr env fn_ptr
              | Some n ->
                  let fn_ptr =
                    {
                      kind = FunId (FRegular merged_method);
                      generics = { fn_ptr.generics with const_generics = [ n ] };
                    }
                  in
                  super#visit_fn_ptr env fn_ptr
            end
          | _ -> super#visit_fn_ptr env fn_ptr
      end
    in
    visitor#visit_crate None crate

exception FoundStatement of statement

(** Charon's structured control-flow reconstruction can encode a function return
    from inside nested loops as a write to local zero followed by loop control.
    Re-expose that control transfer as [Return] before
    [lower_nested_loop_returns] carries it through the loop nest.

    Local zero is LLBC's function return place. We only restore a return when
    the write's immediate remainder is cleanup followed by [Break] or [Return].
    This syntactic guard avoids treating an arbitrary intermediate write to the
    return place as terminal. *)
let restore_structured_nested_returns (_crate : crate) (f : fun_decl) : fun_decl
    =
  match f.body with
  | StructuredBody body ->
      let return_local =
        match body.locals.locals with
        | return_local :: _ -> return_local.index
        | [] -> [%internal_error] f.item_meta.span
      in
      let writes_return_place (st : statement) =
        match st.kind with
        | Assign ({ kind = PlaceLocal local; _ }, _) -> local = return_local
        | Call ({ dest = { kind = PlaceLocal local; _ }; _ }, _) ->
            local = return_local
        | _ -> false
      in
      (* Track only a syntactically cleanup-only continuation to the function
         return.  A loop break is terminal only if its matching post-loop
         continuation is itself cleanup-only and reaches that return. *)
      let rec continuation_returns outer_fallthrough break_returns = function
        | [] -> outer_fallthrough
        | { kind = Return; _ } :: _ -> true
        | { kind = Break index; _ } :: _ ->
            Option.value ~default:false (List.nth_opt break_returns index)
        | { kind = StorageDead _ | Nop; _ } :: rest ->
            continuation_returns outer_fallthrough break_returns rest
        | { kind = Drop _; _ } :: rest when !Config.drop_as_no_op ->
            continuation_returns outer_fallthrough break_returns rest
        | { kind = Assign ({ kind = PlaceLocal local; _ },
              Use (Constant { kind = CLiteral (VBool _); _ }, _)); _ } :: rest
            when !Config.drop_as_no_op && local <> return_local ->
            continuation_returns outer_fallthrough break_returns rest
        | _ -> false
      in
      let rec transform_block depth break_returns outer_fallthrough
          (block : block) : block =
        { block with statements =
            transform_statements depth break_returns outer_fallthrough
              block.statements }
      and transform_statements depth break_returns outer_fallthrough = function
        | (write : statement) :: rest
          when depth > 0 && writes_return_place write -> (
            let drop_noop_cleanup_block (block : block) : bool * bool =
              List.fold_left
                (fun (valid, saw_drop) (st : statement) ->
                  match st.kind with
                  | StorageDead _ | Nop -> (valid, saw_drop)
                  | Drop _ -> (valid, true)
                  | _ -> (false, saw_drop))
                (true, false) block.statements
            in
            let is_drop_noop_switch then_block else_block =
              let then_valid, then_drop =
                drop_noop_cleanup_block then_block
              in
              let else_valid, else_drop =
                drop_noop_cleanup_block else_block
              in
              then_valid && else_valid && (then_drop || else_drop)
            in
            let is_cleanup_then_return (block : block) =
              match List.rev block.statements with
              | { kind = Return; _ } :: reversed_cleanup ->
                  reversed_cleanup <> []
                  && fst
                       (drop_noop_cleanup_block
                          { block with statements = List.rev reversed_cleanup })
              | _ -> false
            in
            let is_split_drop_return then_block else_block =
              (then_block.statements = []
              && is_cleanup_then_return else_block)
              || (else_block.statements = []
                 && is_cleanup_then_return then_block)
            in
            let is_empty_match branches otherwise =
              match (branches, otherwise) with
              | [ (_, ({ statements = []; _ } : block)) ],
                Some ({ statements = []; _ } : block) ->
                  true
              | _ -> false
            in
            let rec take_cleanup reversed = function
              | ({ kind = StorageDead _ | Nop; _ } as cleanup) :: tail ->
                  take_cleanup (cleanup :: reversed) tail
              | ({ kind = Drop _; _ } as cleanup) :: tail
                when !Config.drop_as_no_op ->
                  take_cleanup (cleanup :: reversed) tail
              | ( {
                    kind =
                      Assign
                        ( { kind = PlaceLocal local; _ },
                          Use
                            (Constant { kind = CLiteral (VBool _); _ }, _) );
                    _;
                  } as cleanup )
                :: tail
                when !Config.drop_as_no_op && local <> return_local ->
                  take_cleanup (cleanup :: reversed) tail
              | ( {
                    kind =
                      Switch
                        (If
                          ( Copy { kind = PlaceLocal _; _ }, then_block,
                            else_block ));
                    _;
                  } as cleanup )
                :: tail
                when !Config.drop_as_no_op
                     && (is_drop_noop_switch then_block else_block
                        || is_split_drop_return then_block else_block) ->
                  take_cleanup (cleanup :: reversed) tail
              | ( {
                    kind =
                      Switch
                        (Match
                          ( { kind = PlaceLocal _; _ }, branches,
                            otherwise ));
                    _;
                  } as cleanup )
                :: tail
                when is_empty_match branches otherwise ->
                  take_cleanup (cleanup :: reversed) tail
              | tail -> (List.rev reversed, tail)
            in
            let cleanup, tail = take_cleanup [] rest in
            match tail with
            | ({ kind = Return; _ } as leave) :: _ ->
                (write :: cleanup) @ [ leave ]
            | ({ kind = Break index; _ } as leave) :: _
              when Option.value ~default:false
                     (List.nth_opt break_returns index) ->
                (write :: cleanup) @ [ { leave with kind = Return } ]
            | [] when outer_fallthrough ->
                (* The branch rejoins only cleanup and the known function
                   return. Re-expose that return before loop lowering. *)
                (write :: cleanup)
                @ [ { write with kind = Return; comments_before = [] } ]
            | _ ->
                transform_statement depth break_returns
                  (continuation_returns outer_fallthrough break_returns rest)
                  write
                :: transform_statements depth break_returns outer_fallthrough rest)
        | st :: rest ->
            transform_statement depth break_returns
              (continuation_returns outer_fallthrough break_returns rest) st
            :: transform_statements depth break_returns outer_fallthrough rest
        | [] -> []
      and transform_statement depth break_returns child_fallthrough
          (st : statement) : statement =
        match st.kind with
        | Loop loop ->
            { st with kind = Loop
                (transform_block (depth + 1)
                  (child_fallthrough :: break_returns) false loop) }
        | _ ->
            let visitor =
              object
                inherit [_] map_statement_base
                method! visit_block _ block =
                  transform_block depth break_returns child_fallthrough block
              end
            in
            visitor#visit_statement () st
      in
      let body = { body with body = transform_block 0 [] false body.body } in
      { f with body = StructuredBody body }
  | _ -> f

(** Lower function returns from nested loops before {!update_loops}.

    The symbolic loop interpreter handles nested loops, but a function return
    cannot cross more than one loop boundary directly. We make that control
    transfer explicit with one fresh [Option<return_type>] local. The option
    carries the return value as well as the control signal; this matters because
    the ordinary function return place is uninitialized on non-return paths:

    {[
      loop {
        loop {
          if p { return }
        }
      }

        ~~>

      pending_return := None;
      loop {
        loop {
          if p {
            pending_return := Some(move return_place);
            break 0
          }
        };
        match pending_return { Some(_) => break 0, None => () }
      };
      match pending_return {
        Some(value) => { return_place := move value; return },
        None => ()
      }
    ]}

    A propagation check is inserted immediately after every loop containing a
    lowered return. At an inner level it breaks the immediately enclosing loop;
    after an outermost loop it restores the carried value to the return place
    and performs the original return. Normal breaks and continues leave the
    option at [None] and retain their original behaviour.

    The pass activates only for functions which actually contain a return under
    a loop. In such a function all returns under a loop are lowered uniformly,
    so the loop interpreter never has to distinguish an original return from a
    propagated one. Newly-created statements receive id zero; the existing
    statement-id refresh pass assigns their final ids. *)
let lower_nested_loop_returns (crate : crate) (f : fun_decl) : fun_decl =
  match f.body with
  | StructuredBody body ->
      let has_nested_return =
        let visitor =
          object
            inherit [_] iter_statement as super
            method! visit_Loop depth loop = super#visit_Loop (depth + 1) loop
            method! visit_Return depth = if depth >= 1 then raise Found
          end
        in
        try
          visitor#visit_block 0 body.body;
          false
        with Found -> true
      in
      if not has_nested_return then f
      else
        let option_ids =
          TypeDeclId.Map.fold
            (fun id (decl : type_decl) ids ->
              if decl.item_meta.lang_item = Some "Option" then id :: ids
              else ids)
            crate.type_decls []
        in
        let option_id =
          match option_ids with
          | [ id ] -> id
          | _ ->
              [%craise] f.item_meta.span
                "Nested-loop returns require exactly one Option language item"
        in
        let return_local =
          match body.locals.locals with
          | return_local :: _ -> return_local
          | [] -> [%internal_error] f.item_meta.span
        in
        let return_ty = return_local.local_ty in
        let option_ref : type_decl_ref =
          {
            id = TAdtId option_id;
            generics = TypesUtils.mk_generic_args [] [ return_ty ] [] [];
          }
        in
        let pending_ty = TAdt option_ref in
        let _, gen =
          LocalId.mk_stateful_generator_starting_at_id
            (LocalId.of_int (List.length body.locals.locals))
        in
        let pending_local : local =
          {
            index = gen ();
            local_ty = pending_ty;
            name = Some "pending_return";
            span = f.item_meta.span;
          }
        in
        let pending_place : place =
          { kind = PlaceLocal pending_local.index; ty = pending_ty }
        in
        let capture_local : local =
          {
            index = gen ();
            local_ty = return_ty;
            name = Some "return_capture";
            span = f.item_meta.span;
          }
        in
        let capture_place : place =
          { kind = PlaceLocal capture_local.index; ty = return_ty }
        in
        let return_place : place =
          { kind = PlaceLocal return_local.index; ty = return_ty }
        in
        let writes_return_place (st : statement) =
          match st.kind with
          | Assign ({ kind = PlaceLocal local; _ }, _) ->
              local = return_local.index
          | Call ({ dest = { kind = PlaceLocal local; _ }; _ }, _) ->
              local = return_local.index
          | _ -> false
        in
        let retarget_return_write (st : statement) : statement =
          match st.kind with
          | Assign ({ kind = PlaceLocal local; _ }, rv)
            when local = return_local.index ->
              { st with kind = Assign (capture_place, rv) }
          | Call
              ( ({ dest = { kind = PlaceLocal local; _ }; _ } as call),
                on_unwind )
            when local = return_local.index ->
              { st with kind = Call ({ call with dest = capture_place }, on_unwind) }
          | _ -> [%internal_error] st.span
        in
        let mk_statement ?(comments_before = []) span kind : statement =
          { span; statement_id = StatementId.zero; kind; comments_before }
        in
        let fresh_cleanup (cleanup : statement list) : statement list =
          List.map
            (fun (st : statement) ->
              { st with statement_id = StatementId.zero })
            cleanup
        in
        let mk_pending_assignment ?(comments_before = []) span variant fields =
          mk_statement ~comments_before span
            (Assign
               ( pending_place,
                 Aggregate
                   (AggregatedAdt (option_ref, Some variant, None), fields) ))
        in
        let block_contains_return (block : block) : bool =
          let visitor =
            object
              inherit [_] iter_statement
              method! visit_Return _ = raise Found
            end
          in
          try
            visitor#visit_block () block;
            false
          with Found -> true
        in
        let propagation_check span depth reject_none loop_exit_cleanup :
            statement =
          let action =
            if depth = 0 then
              let payload_place : place =
                {
                  kind =
                    PlaceProjection
                      ( pending_place,
                        Field
                          ( ProjAdt (option_id, Some Types.option_some_id),
                            FieldId.of_int 0 ) );
                  ty = return_ty;
                }
              in
              [
                mk_statement span
                  (Assign (return_place, Use (Move payload_place, NoRetag)));
                mk_statement span Return;
              ]
            else
              fresh_cleanup loop_exit_cleanup @ [ mk_statement span (Break 0) ]
          in
          let then_block = { span; statements = action } in
          let else_block =
            {
              span;
              statements =
                (if reject_none then
                   [ mk_statement span (Abort UndefinedBehavior) ]
                 else []);
            }
          in
          mk_statement span
            (Switch
               (Match
                  ( pending_place,
                    [ ([ Types.option_some_id ], then_block) ],
                    Some else_block )))
        in
        (* A cleanup-only bare return after the outer loop reads LLBC local
           zero. If no earlier top-level statement wrote that local, Rust's
           definite-initialization rules mean the loop cannot reach that
           return without one of the carried nested returns. Keeping an
           explicit abort in the impossible [None] arm prevents the symbolic
           interpreter from inventing an uninitialized fallthrough path. *)
        let rec cleanup_then_bare_return = function
          | { kind = StorageDead _ | Nop; _ } :: rest ->
              cleanup_then_bare_return rest
          | [ { kind = Return; _ } ] -> true
          | _ -> false
        in
        (* A loop can be nested under several switch branches while its normal
           fallthrough still reaches the function's cleanup-only bare return.
           Propagate that fact across statements which cannot initialize the
           return place. *)
        let rec cleanup_falls_through_to_return outer_fallthrough = function
          | [] -> outer_fallthrough
          | { kind = StorageDead _ | Nop | Drop _; _ } :: rest ->
              cleanup_falls_through_to_return outer_fallthrough rest
          | [ { kind = Return; _ } ] -> true
          | _ -> false
        in
        let lowered_return (st : statement) : statement * statement =
          ( mk_pending_assignment ~comments_before:st.comments_before st.span
              Types.option_some_id [ Move return_place ],
            { st with kind = Break 0; comments_before = [] } )
        in
        let rec take_cleanup reversed = function
          | ({ kind = StorageDead _ | Nop; _ } as cleanup) :: rest ->
              take_cleanup (cleanup :: reversed) rest
          | rest -> (List.rev reversed, rest)
        in
        (* A Rust return drops every live owned local before leaving the
           function.  Once that return is carried through an enclosing loop,
           those function-exit drops must travel with the return rather than
           execute before the loop join: the ordinary branch still owns the
           values.  In the default mode drops are explicitly interpreted as
           no-ops, so replace the complete drop/dead sequence with the cleanup
           for a normal exit from the current loop.  Keep explicit drops when
           [-eval-drops] requests their semantics. *)
        let drop_noop_cleanup_block (block : block) : bool * bool =
          List.fold_left
            (fun (valid, saw_drop) (st : statement) ->
              match st.kind with
              | StorageDead _ | Nop -> (valid, saw_drop)
              | Drop _ -> (valid, true)
              | _ -> (false, saw_drop))
            (true, false) block.statements
        in
        let is_drop_noop_switch then_block else_block =
          let then_valid, then_drop = drop_noop_cleanup_block then_block in
          let else_valid, else_drop = drop_noop_cleanup_block else_block in
          then_valid && else_valid && (then_drop || else_drop)
        in
        let is_cleanup_then_return (block : block) =
          match List.rev block.statements with
          | { kind = Return; _ } :: reversed_cleanup ->
              reversed_cleanup <> []
              && fst
                   (drop_noop_cleanup_block
                      { block with statements = List.rev reversed_cleanup })
          | _ -> false
        in
        let is_split_drop_return then_block else_block =
          (then_block.statements = [] && is_cleanup_then_return else_block)
          || (else_block.statements = [] && is_cleanup_then_return then_block)
        in
        let is_empty_match branches otherwise =
          match (branches, otherwise) with
          | [ (_, ({ statements = []; _ } : block)) ],
            Some ({ statements = []; _ } : block) ->
              true
          | _ -> false
        in
        let rec take_return_cleanup reversed = function
          | ({ kind = StorageDead _ | Nop; _ } as cleanup) :: rest ->
              take_return_cleanup (cleanup :: reversed) rest
          | ({ kind = Drop _; _ } as cleanup) :: rest
            when !Config.drop_as_no_op ->
              take_return_cleanup (cleanup :: reversed) rest
          | ( {
                kind =
                  Assign
                    ( { kind = PlaceLocal local; _ },
                      Use (Constant { kind = CLiteral (VBool _); _ }, _) );
                _;
              } as cleanup )
            :: rest
            when !Config.drop_as_no_op && local <> return_local.index ->
              take_return_cleanup (cleanup :: reversed) rest
          | ( {
                kind =
                  Switch
                    (If
                      ( Copy { kind = PlaceLocal _; _ }, then_block,
                        else_block ));
                _;
              } as cleanup )
            :: rest
            when !Config.drop_as_no_op
                 && (is_drop_noop_switch then_block else_block
                    || is_split_drop_return then_block else_block) ->
              take_return_cleanup (cleanup :: reversed) rest
          | ( {
                kind =
                  Switch
                    (Match
                      ( { kind = PlaceLocal _; _ }, branches, otherwise ));
                _;
              } as cleanup )
            :: rest
            when is_empty_match branches otherwise ->
              take_return_cleanup (cleanup :: reversed) rest
          | rest -> (List.rev reversed, rest)
        in
        (* Charon can encode the normal exit from a reconstructed [for] loop
           as a continue to an enclosing loop.  In that case the statements
           after the inner [Loop] are an unreachable fallback whose cleanup
           may also kill state owned by the enclosing loop.  If that fallback
           is copied onto a lowered return, Aeneas joins the dead enclosing
           iterator into the ordinary path out of the inner loop.

           Recover the cleanup common to the loop's actual non-return exits.
           We inspect this loop body but skip nested loops, collect the trailing
           [StorageDead] locals before a current-loop break or an outward
           break/continue, and retain their intersection. *)
        let loop_normal_exit_cleanup (loop : block) : statement list option =
          let exits : statement list list ref = ref [] in
          let saw_outward_exit = ref false in
          let is_cleanup (st : statement) =
            match st.kind with
            | StorageDead _ | Nop -> true
            | _ -> false
          in
          let is_normal_exit (st : statement) =
            match st.kind with
            | Break index when index > 0 ->
                saw_outward_exit := true;
                true
            | Break 0 -> true
            | Continue index when index > 0 ->
                saw_outward_exit := true;
                true
            | _ -> false
          in
          let rec scan_block (block : block) =
            scan_statements [] block.statements
          and scan_statements reversed_cleanup = function
            | st :: rest when is_cleanup st ->
                scan_statements (st :: reversed_cleanup) rest
            | st :: rest ->
                if is_normal_exit st then
                  exits := List.rev reversed_cleanup :: !exits
                else
                  let visitor =
                    object
                      inherit [_] iter_statement_base
                      method! visit_Loop _ _ = ()
                      method! visit_block _ block = scan_block block
                    end
                  in
                  visitor#visit_statement () st;
                  scan_statements [] rest
            | [] -> ()
          in
          scan_block loop;
          match (!saw_outward_exit, List.rev !exits) with
          | false, _ -> None
          | true, [] -> None
          | true, first :: remaining ->
              let dead_locals cleanup =
                List.fold_left
                  (fun locals (st : statement) ->
                    match st.kind with
                    | StorageDead local -> LocalId.Set.add local locals
                    | Nop -> locals
                    | _ -> [%internal_error] st.span)
                  LocalId.Set.empty cleanup
              in
              let common =
                List.fold_left
                  (fun common cleanup ->
                    LocalId.Set.inter common (dead_locals cleanup))
                  (dead_locals first) remaining
              in
              Some
                (List.filter
                   (fun (st : statement) ->
                     match st.kind with
                     | StorageDead local -> LocalId.Set.mem local common
                     | Nop -> false
                     | _ -> false)
                   first)
        in
        let rec transform_block depth loop_exit_cleanup outer_fallthrough
            (block : block) : block =
          {
            block with
            statements =
              transform_statements depth loop_exit_cleanup outer_fallthrough
                false block.statements;
          }
        and transform_statements depth loop_exit_cleanup outer_fallthrough
            return_written = function
          | [] -> []
          | (write : statement) :: statements
            when depth > 0 && writes_return_place write -> (
              let cleanup, rest = take_return_cleanup [] statements in
              match rest with
              | ({ kind = Return; _ } as return_st) :: tail ->
                  let child_fallthrough =
                    cleanup_falls_through_to_return outer_fallthrough statements
                  in
                  let transformed_write =
                    transform_statement depth loop_exit_cleanup
                      child_fallthrough (retarget_return_write write)
                  in
                  let assignment =
                    mk_pending_assignment
                      ~comments_before:return_st.comments_before return_st.span
                      Types.option_some_id [ Move capture_place ]
                  in
                  let leave =
                    { return_st with kind = Break 0; comments_before = [] }
                  in
                  transformed_write
                  @ fresh_cleanup loop_exit_cleanup
                  @ [ assignment; leave ]
                  @ transform_statements depth loop_exit_cleanup
                      outer_fallthrough return_written tail
              | _ ->
                  transform_noncleanup_statement depth loop_exit_cleanup
                    outer_fallthrough return_written (write :: statements))
          | statements when depth > 0 -> (
              let cleanup, rest = take_return_cleanup [] statements in
              match (cleanup, rest) with
              | _ :: _, ({ kind = Return; _ } as return_st) :: tail ->
                  (* Use the cleanup common to this loop's ordinary exits. *)
                  let assignment, leave = lowered_return return_st in
                  fresh_cleanup loop_exit_cleanup
                  @ [ assignment; leave ]
                  @ transform_statements depth loop_exit_cleanup
                      outer_fallthrough return_written tail
              | _ ->
                  transform_noncleanup_statement depth loop_exit_cleanup
                    outer_fallthrough return_written statements)
          | statements ->
              transform_noncleanup_statement depth loop_exit_cleanup
                outer_fallthrough return_written statements
        and transform_noncleanup_statement depth loop_exit_cleanup
            outer_fallthrough return_written = function
          | [] -> []
          | ({ kind = Loop loop; _ } as st) :: rest ->
              let reject_none =
                depth = 0 && (not return_written)
                && (cleanup_then_bare_return rest
                   || cleanup_falls_through_to_return outer_fallthrough rest)
              in
              let contains_return = block_contains_return loop in
              if contains_return then
                (* The cleanup immediately following a structured loop ends
                   the iterator state shared by all of its exits. Move copies
                   of it before every exit from the transformed loop, so the
                   loop interpreter never has to join a live iterator with an
                   already-ended one. *)
                let cleanup, tail = take_cleanup [] rest in
                let loop_cleanup =
                  Option.value ~default:cleanup (loop_normal_exit_cleanup loop)
                in
                let loop =
                  transform_block (depth + 1) loop_cleanup false loop
                in
                let loop_st = { st with kind = Loop loop } in
                loop_st
                :: propagation_check st.span depth reject_none loop_exit_cleanup
                :: transform_statements depth loop_exit_cleanup
                     outer_fallthrough return_written tail
              else
                (* A loop without a nested return still needs its immediate
                   post-loop lifetime cleanup on every break.  Otherwise a
                   mutable iterator handback can escape into loop synthesis
                   even though the corresponding Rust temporary is dead on
                   every path which leaves the loop. *)
                let cleanup, tail = take_cleanup [] rest in
                let loop_cleanup =
                  Option.value ~default:cleanup (loop_normal_exit_cleanup loop)
                in
                let loop =
                  transform_block (depth + 1) loop_cleanup false loop
                in
                let loop_st = { st with kind = Loop loop } in
                loop_st
                :: transform_statements depth loop_exit_cleanup
                     outer_fallthrough return_written tail
          | (st : statement) :: rest ->
              let child_fallthrough =
                cleanup_falls_through_to_return outer_fallthrough rest
              in
              let transformed =
                transform_statement depth loop_exit_cleanup child_fallthrough st
              in
              let return_written = return_written || writes_return_place st in
              transformed
              @ transform_statements depth loop_exit_cleanup outer_fallthrough
                  return_written rest
        and transform_statement depth loop_exit_cleanup child_fallthrough
            (st : statement) : statement list =
          match st.kind with
          | Return when depth > 0 ->
              let assignment, leave = lowered_return st in
              fresh_cleanup loop_exit_cleanup @ [ assignment; leave ]
          | Break 0 when depth > 0 -> fresh_cleanup loop_exit_cleanup @ [ st ]
          | Loop _ -> [%internal_error] st.span
          | _ ->
              let visitor =
                object
                  inherit [_] map_statement

                  method! visit_block child_depth child =
                    transform_block child_depth loop_exit_cleanup
                      child_fallthrough child
                end
              in
              [ visitor#visit_statement depth st ]
        in
        let initialization =
          mk_pending_assignment f.item_meta.span Types.option_none_id []
        in
        let body_body = transform_block 0 [] false body.body in
        let body_body =
          { body_body with statements = initialization :: body_body.statements }
        in
        let locals =
          {
            body.locals with
            locals = body.locals.locals @ [ pending_local; capture_local ];
          }
        in
        { f with body = StructuredBody { body with body = body_body; locals } }
  | _ -> f

(* The [update_loops] pass below checks that loops:
    - do not contain early returns
    - do not continue/break to outer loops

    We also attempt to update the loops so that they have the proper shape (for
    instance, if a loop has returns but no breaks, we replace the returns with
    breaks, and move the returns after the loop).

    We do the following transformations:

    # Transformation 1:
    {[
      loop {
        if e {
          return;
        } else {
          continue;
        }
      }

        ~~>

      loop {
        if e {
          break;
        } else {
          continue;
        }
      };
      return;
    ]}

    # Transformation 2:
    {[
      loop {
        if e0 {
          st0;
          return;
        } else if e1 {
          st1;
          break;
        } else {
          continue;
        }
      }
      st2;
      return;

        ~~>

      loop {
        if e0 {
          st0;
          break;
        } else if e1 {
          st1;
          st2;
          break;
        } else {
          continue;
        }
      }
      return;
    ]}

    # Transformation 3:
    {[
      loop {
        if e0 {
          st0;
          return;
        } else if e1 {
          st1;
          break;
        } else {
          continue;
        }
      }
      st2;
      panic;

        ~~>

      loop {
        if e0 {
          st0;
          break;
        } else if e1 {
          st1;
          st2;
          panic;
        } else {
          continue;
        }
      }
      return;
    ]} *)
type outer_loop_control = OuterBreak of int | OuterContinue of int

(** Eliminate [Break]/[Continue] statements which target an enclosing loop.

    The symbolic loop interpreter deliberately accepts only control transfers
    for the loop it is currently translating. Charon represents a labelled
    transfer from an inner loop to an enclosing loop with a positive index. For
    each loop containing such transfers, this pass introduces a fresh integer
    control local and lowers, for example:

    {[
      loop {
        ...;
        continue 1
      }

        ~~>

      control = 0;
      loop {
        ...;
        control = 1;
        break 0
      };
      switch control {
        1 => continue 0,
        _ => ()
      }
    ]}

    Every distinct [(kind, index)] pair gets its own nonzero code. The switch
    decrements the index by exactly one, so processing loops from the inside out
    propagates transfers across one loop boundary at a time. Ordinary
    fallthrough, [break 0], and [continue 0] leave the control local at zero.

    The control local is live only around the transformed loop and is killed on
    every post-loop branch before the transfer is re-emitted. Mutations before a
    transfer therefore happen before the control write, while statements after
    it remain unreachable because the replacement ends in [break 0].

    This pass intentionally does not lower [Return]. A return-unwinding pass can
    run immediately before this one: the [break 0] statements it introduces are
    left untouched. *)
let eliminate_outer_loop_control (crate : crate) (f : fun_decl) : fun_decl =
  let f0 = f in
  match f.body with
  | StructuredBody body ->
      let control_literal_ty : literal_type = TUInt U32 in
      let control_ty = TLiteral control_literal_ty in
      let new_locals = ref [] in
      let _, gen_local =
        LocalId.mk_stateful_generator_starting_at_id
          (LocalId.of_int (List.length body.locals.locals))
      in
      let fresh_control_local span =
        let local =
          { index = gen_local (); local_ty = control_ty; name = None; span }
        in
        new_locals := local :: !new_locals;
        local.index
      in
      let mk_statement span comments_before kind : statement =
        { span; statement_id = StatementId.zero; kind; comments_before }
      in
      let mk_control_literal code : Values.literal =
        VScalar (UnsignedScalar (U32, Z.of_int code))
      in
      let mk_control_operand code : operand =
        Constant { kind = CLiteral (mk_control_literal code); ty = control_ty }
      in
      let action_equal left right =
        match (left, right) with
        | OuterBreak i, OuterBreak j | OuterContinue i, OuterContinue j -> i = j
        | _ -> false
      in
      let rec transform_block (block : block) : block =
        {
          block with
          statements =
            List.flatten (List.map transform_statement block.statements);
        }
      and transform_statement (st : statement) : statement list =
        match st.kind with
        | Loop loop ->
            (* Transform nested loops before lowering transfers out of this
               loop.  A transfer crossing several boundaries is consequently
               propagated one boundary per recursive return. *)
            let loop = transform_block loop in
            let actions = ref [] in
            let add_action action =
              if not (List.exists (action_equal action) !actions) then
                actions := !actions @ [ action ]
            in
            let collector =
              object
                inherit [_] iter_statement_base as super
                method! visit_Loop _ _ = ()

                method! visit_Break env index =
                  if index > 0 then add_action (OuterBreak index)
                  else super#visit_Break env index

                method! visit_Continue env index =
                  if index > 0 then add_action (OuterContinue index)
                  else super#visit_Continue env index
              end
            in
            collector#visit_block () loop;
            if !actions = [] then [ { st with kind = Loop loop } ]
            else
              let control_local = fresh_control_local st.span in
              let control_place =
                { kind = PlaceLocal control_local; ty = control_ty }
              in
              let code_for action =
                let rec find code = function
                  | [] -> [%internal_error] st.span
                  | candidate :: remaining ->
                      if action_equal action candidate then code
                      else find (code + 1) remaining
                in
                find 1 !actions
              in
              let set_control_and_break (original : statement)
                  (action : outer_loop_control) : statement list =
                let set_control =
                  mk_statement original.span original.comments_before
                    (Assign
                       ( control_place,
                         Use (mk_control_operand (code_for action), NoRetag) ))
                in
                let leave_current_loop =
                  mk_statement original.span [] (Break 0)
                in
                [ set_control; leave_current_loop ]
              in
              let rec rewrite_block (block : block) : block =
                {
                  block with
                  statements =
                    List.flatten (List.map rewrite_statement block.statements);
                }
              and rewrite_statement (inner_st : statement) : statement list =
                match inner_st.kind with
                | Loop _ ->
                    (* Nested loops were already transformed.  Do not interpret
                       their local control transfers relative to this loop. *)
                    [ inner_st ]
                | Break index when index > 0 ->
                    set_control_and_break inner_st (OuterBreak index)
                | Continue index when index > 0 ->
                    set_control_and_break inner_st (OuterContinue index)
                | _ ->
                    let child_rewriter =
                      object
                        inherit [_] map_statement_base
                        method! visit_block _ block = rewrite_block block
                      end
                    in
                    [ child_rewriter#visit_statement () inner_st ]
              in
              let loop = rewrite_block loop in
              let storage_live =
                mk_statement st.span [] (StorageLive control_local)
              in
              let initialize =
                mk_statement st.span []
                  (Assign (control_place, Use (mk_control_operand 0, NoRetag)))
              in
              let loop_statement = { st with kind = Loop loop } in
              let branch_for action =
                let propagated =
                  match action with
                  | OuterBreak index -> Break (index - 1)
                  | OuterContinue index -> Continue (index - 1)
                in
                let block =
                  {
                    span = st.span;
                    statements =
                      [
                        mk_statement st.span [] (StorageDead control_local);
                        mk_statement st.span [] propagated;
                      ];
                  }
                in
                ([ mk_control_literal (code_for action) ], block)
              in
              let otherwise =
                {
                  span = st.span;
                  statements =
                    [ mk_statement st.span [] (StorageDead control_local) ];
                }
              in
              let dispatch =
                mk_statement st.span []
                  (Switch
                     (SwitchInt
                        ( Copy control_place,
                          control_literal_ty,
                          List.map branch_for !actions,
                          otherwise )))
              in
              [ storage_live; initialize; loop_statement; dispatch ]
        | _ ->
            let nested_loop_rewriter =
              object
                inherit [_] map_statement_base
                method! visit_block _ block = transform_block block
              end
            in
            [ nested_loop_rewriter#visit_statement () st ]
      in
      let body_body = transform_block body.body in
      let locals =
        { body.locals with locals = body.locals.locals @ List.rev !new_locals }
      in
      let f =
        { f with body = StructuredBody { body with body = body_body; locals } }
      in
      [%ldebug
        let env = Print.crate_to_fmt_env crate in
        "Before/after [eliminate_outer_loop_control]:\n"
        ^ Print.fun_decl_to_string env "" " " f0
        ^ "\n\n"
        ^ Print.fun_decl_to_string env "" " " f];
      f
  | _ -> f

(** Apply the early-return loop transformations described above and reject any
    unsupported loop control which remains after the dedicated prepasses. *)
let update_loops (crate : crate) (f : fun_decl) : fun_decl =
  let f0 = f in
  let span = f.item_meta.span in

  let visitor =
    object (self)
      inherit [_] map_statement as super

      (* [after]: the list of statements coming *after* this one in this block.

         We return:
         - the list of statements resulting from updating the current statement
         - the list of statements to put after and that are yet to be updated
           (the reason is that we might have moved some of those statements
           inside the current statement).
      *)
      method update_statement (depth : int) (st : statement)
          (after : statement list) : statement list * statement list =
        match st.kind with
        | Loop loop -> (
            (* Recursively update the loop.

               Note that doing this will raise an exception if we find a loop with
               an early return. *)
            try ([ { st with kind = self#visit_Loop (depth + 1) loop } ], after)
            with FoundStatement return_st ->
              (* An exception was raised: it means we found a return in the loop: attempt
                 to replace it with a break.

                 There are 2 cases:
                 - either the loop does not contain any break, in which case we
                   can simply replace the return with a break, and move the return
                   after the loop (this is transformation 1 above)
                 - or there is already a break in the loop: we can apply transformation 2
                   (resp., 3) if the statements after the loop end with a return (resp., a panic)
              *)
              let block_has_no_breaks (b : block) : bool =
                let visitor =
                  object
                    inherit [_] iter_statement
                    method! visit_Break _ _ = raise Found
                  end
                in
                try
                  visitor#visit_block () b;
                  true
                with Found -> false
              in
              if block_has_no_breaks loop then (* Transformation 1 *)
                let block_replace (b : block) : block =
                  let visitor =
                    object
                      inherit [_] map_statement
                      method! visit_Loop i loop = super#visit_Loop (i + 1) loop

                      method! visit_Return i =
                        [%sanity_check] span (i = 0);
                        (* Replace the return with a break *)
                        Break i
                    end
                  in
                  visitor#visit_block 0 b
                in
                let loop = block_replace loop in
                let loop : statement = { st with kind = Loop loop } in
                let loop = super#visit_statement depth loop in
                let return : statement =
                  {
                    span = st.span;
                    statement_id =
                      StatementId.zero (* we'll refresh this later *);
                    kind = Return;
                    comments_before = [];
                  }
                in
                ([ loop; return ], after)
              else
                (* Transformations 2 and 3 *)
                (* Check if the statements after the loop end with a return or a panic.
                   We output the statements with which to replace breaks.
                *)
                let rec decompose_after (after : statement list) :
                    statement list =
                  match after with
                  | [] ->
                      [%craise] span
                        "Early returns inside of loops are not supported yet"
                  | st :: after -> (
                      match st.kind with
                      | Return -> [ { st with kind = Break 0 } ]
                      | Abort _ -> [ st ]
                      | _ -> st :: decompose_after after)
                in
                let after = decompose_after after in
                let replace (st : statement) : statement list =
                  match st.kind with
                  | Return ->
                      (* Replace the return with a break *)
                      [ { st with kind = Break 0 } ]
                  | Break i ->
                      (* Move the statements [after] before the break *)
                      [%cassert] span (i = 0)
                        "Breaks to outer loops are not supported yet";
                      after
                  | _ -> [ st ]
                in

                let block_visitor =
                  object (self)
                    inherit [_] map_statement_base as super

                    method! visit_Loop depth loop =
                      super#visit_Loop (depth + 1) loop

                    method! visit_block depth b =
                      (* Only replace if the depth is 0 (it means we haven't dived
                         into an inner loop) *)
                      if depth = 0 then
                        let update st =
                          replace (self#visit_statement depth st)
                        in
                        {
                          b with
                          statements =
                            List.flatten (List.map update b.statements);
                        }
                      else b
                  end
                in

                let loop = block_visitor#visit_block 0 loop in
                let loop : statement = { st with kind = Loop loop } in
                let loop = super#visit_statement depth loop in
                ([ loop; return_st ], []))
        | _ -> ([ self#visit_statement depth st ], after)

      method! visit_block depth (block : block) : block =
        let rec update (stl : statement list) : statement list =
          match stl with
          | [] -> []
          | st :: stl ->
              let stl0, stl1 = self#update_statement depth st stl in
              stl0 @ update stl1
        in
        { block with statements = update block.statements }

      method! visit_Break depth i =
        [%cassert] span (i = 0) "Breaks to outer loops are not supported yet";
        super#visit_Break depth i

      method! visit_Continue depth i =
        [%cassert] span (i = 0) "Continue to outer loops are not supported yet";
        super#visit_Continue depth i

      method! visit_statement depth st =
        match st.kind with
        | Return ->
            [%cassert] span (depth <= 1)
              "Returns inside of nested loops are not supported yet";
            (* If we are inside a loop we need to get rid of the return.

               Note that raising an exception containing the full return
               statement allows us to use its span when moving it after the loop. *)
            if depth = 1 then raise (FoundStatement st) else st
        | _ -> super#visit_statement depth st

      method! visit_Return _ =
        (* The Return case should have been caught by the [visit_statement] method *)
        [%internal_error] span
    end
  in

  (* Map  *)
  let body =
    match f.body with
    | StructuredBody body ->
        StructuredBody { body with body = visitor#visit_block 0 body.body }
    | other -> other
  in

  let f : fun_decl = { f with body } in
  [%ldebug
    let env = Print.crate_to_fmt_env crate in
    "Before/after [update_loops]:\n"
    ^ Print.fun_decl_to_string env "" " " f0
    ^ "\n\n"
    ^ Print.fun_decl_to_string env "" " " f];
  f

(** Inline what comes after an [if then else], a [switch] or a [match], etc.
    under certain conditions, to prevent useless joins from being performed by
    the symbolic execution.

    The main goal of this pass is to improve the quality of the generated code.
*)
let remove_useless_joins (crate : crate) (f : fun_decl) : fun_decl =
  let f0 = f in

  let rec update_block (to_inline : statement list) (block : block) :
      bool * block =
    let can_inline, statements = update_statements to_inline block.statements in
    (can_inline, { block with statements })
  and update_statements (to_inline : statement list) (ls : statement list) :
      bool * statement list =
    match ls with
    | [] -> (true, to_inline)
    | st :: ls -> (
        [%ldebug
          "ls:\n"
          ^ Print.list_to_string ~sep:"\n" (statement_to_string crate) ls];
        let can_inline, ls = update_statements to_inline ls in
        match st.kind with
        | Nop | StorageLive _ | StorageDead _ | PlaceMention _
        | Drop (_, _, _, _) -> (can_inline, st :: ls)
        | Abort _ | Return | UnwindResume | Break _ | Continue _ ->
            (true, [ st ])
        | Switch switch ->
            [%ldebug "Switch: can_inline: " ^ Print.bool_to_string can_inline];
            (* Attempt to inline inside the body *)
            let to_inline, ls = if can_inline then (ls, []) else ([], ls) in
            let update b = snd (update_block to_inline b) in
            let switch =
              match switch with
              | If (scrut, st0, st1) -> If (scrut, update st0, update st1)
              | SwitchInt (op, ty, branches, otherwise) ->
                  let branches =
                    List.map (fun (pats, br) -> (pats, update br)) branches
                  in
                  let otherwise = update otherwise in
                  SwitchInt (op, ty, branches, otherwise)
              | Match (scrut, branches, otherwise) ->
                  let branches =
                    List.map (fun (id, br) -> (id, update br)) branches
                  in
                  let otherwise = Option.map update otherwise in
                  Match (scrut, branches, otherwise)
            in
            let ls = { st with kind = Switch switch } :: ls in
            [%ldebug
              "after updating the switch:\n"
              ^ Print.list_to_string ~sep:"\n" (statement_to_string crate) ls];
            (false, ls)
        | Loop loop ->
            (* Update the inside of the loop *)
            (false, { st with kind = Loop (snd (update_block [] loop)) } :: ls)
        | Assign (_, rv) -> (
            (* We allow inlining some assignments (otherwise the pass is too restrictive) *)
            match rv with
            | Use _ | RvRef _ | RawPtr _ | NullaryOp _ | Aggregate _ ->
                (can_inline, st :: ls)
            | BinaryOp _ | UnaryOp _ | Discriminant _ | Len _ | Repeat _ ->
                (false, st :: ls))
        | SetDiscriminant _ | Assert (_, _, _) | Call (_, _) | Error _ ->
            (false, st :: ls)
        | _ ->
            [%craise] st.span
              ("unsupported statement: " ^ show_statement_kind st.kind))
  in

  let body =
    match f.body with
    | StructuredBody body ->
        StructuredBody { body with body = snd (update_block [] body.body) }
    | other -> other
  in

  let f : fun_decl = { f with body } in
  [%ldebug
    let env = Print.crate_to_fmt_env crate in
    "Before/after [remove_useless_joins]:\n"
    ^ Print.fun_decl_to_string env "" " " f0
    ^ "\n\n"
    ^ Print.fun_decl_to_string env "" " " f];
  f

(** Remove the use of shallow borrows and the storage live/dead instructions.

    Storage live/dead instructions are not used by the symbolic/concrete
    interpreter, so we can safely remove them.

    Shallow borrows are used in early versions of MIR for the sole use of the
    borrow checker (they have no runtime semantics). They are used to prevent
    match guards from changing a discriminant that is being matched on.

    For instance, let's consider the following Rust code:
    {[
      let mut x = (true, true);
      match x {
          (false, _) => 1,
          (true, _) if { x.0 = false; false } => 0,
          (_, true) => 2,
          (true, _) => 3,
      }
    ]}

    If this code was allowed, it would reach an `unreachable_unchecked` code
    path. Rust disallows this by adding a shallow borrow of each place whose
    discriminant is read, and a fake (removed before codegen) read of that
    borrow.

    We discard these in Aeneas. This does allow more code to pass the
    borrow-checker, but the UB is still correctly caught by the
    evaluator/translation hence the translation is still sound. *)
let remove_shallow_borrows_storage_live_dead (crate : crate) (f : fun_decl) :
    fun_decl =
  let f0 = f in
  let filter_in_body (argument_locals : LocalId.Set.t) (body : block) : block =
    let filtered = ref LocalId.Set.empty in

    let filter_shallow (st : statement) : statement list =
      match st.kind with
      | Assign (p, rv) -> (
          match (p.kind, rv) with
          | PlaceLocal var_id, RvRef (_, BShallow, _) ->
              (* Filter *)
              filtered := LocalId.Set.add var_id !filtered;
              []
          | _ -> [ st ])
      | _ -> [ st ]
    in

    let filter_storage (st : statement) : statement list =
      match st.kind with
      | StorageLive _ -> []
      | StorageDead loc
        when LocalId.Set.mem loc !filtered
             || LocalId.Set.mem loc argument_locals -> []
      | _ -> [ st ]
    in

    (* Filter the variables *)
    let body = map_statement filter_shallow body in
    let body = map_statement filter_storage body in

    (* Check that the filtered variables have completely disappeared from the body *)
    let check_visitor =
      object
        inherit [_] iter_statement as super

        (* Remember the span of the statement we enter *)
        method! visit_statement _ st = super#visit_statement st.span st

        method! visit_local_id span id =
          [%cassert] span
            (not (LocalId.Set.mem id !filtered))
            "Filtered variables should have completely disappeared from the \
             body"
      end
    in
    check_visitor#visit_block body.span body;

    (* Return the updated body *)
    body
  in

  let body =
    match f.body with
    | StructuredBody body ->
        let argument_locals =
          body.locals.locals |> List.tl
          |> Collections.List.prefix body.locals.arg_count
          |> List.map (fun (var : local) -> var.index)
          |> LocalId.Set.of_list
        in
        StructuredBody
          { body with body = filter_in_body argument_locals body.body }
    | other -> other
  in
  let f = { f with body } in
  [%ldebug
    let env = Print.crate_to_fmt_env crate in
    "Before/after [remove_shallow_borrows]:\n"
    ^ Print.fun_decl_to_string env "" " " f0
    ^ "\n\n"
    ^ Print.fun_decl_to_string env "" " " f];
  f

(** Strip unnecessary [PeTarget] suffixes from function and type names.

    Multi-target extraction appends [PeTarget] to per-target item names to
    disambiguate items that exist for multiple targets.

    For functions: if the function is not behind a target dispatch (its [src] is
    NOT [TargetDependentItem]), there is no ambiguity (the function is not used
    for several targets), so we remove the suffix.

    For types there is no notion of dispatch, meaning we can't use the item
    source. Instead, we compute a multi-set of base names (names without the
    [PeTarget] suffix) if a type has a suffix but its base name only appears
    once, it means there is no collision and the suffix is unnecessary. *)
let strip_unnecessary_target_suffixes (crate : crate) : crate =
  let module NameMap = Map.Make (struct
    type t = Types.name

    let compare = Types.compare_name
  end) in
  let add_name acc name =
    let base = strip_target_suffix name in
    let count =
      match NameMap.find_opt base acc with
      | Some n -> n
      | None -> 0
    in
    NameMap.add base (count + 1) acc
  in
  let get_name base_counts name =
    let base = strip_target_suffix name in
    if base = name then name
    else
      let count =
        match NameMap.find_opt base base_counts with
        | Some n -> n
        | None -> 0
      in
      if count <= 1 then base else name
  in
  (* --- Functions --- *)
  (* We also count how many non-dispatch functions share a base name.

     We shouldn't need to do this, but have to do it because of:
     https://github.com/AeneasVerif/charon/issues/1158

     Generally speaking it's a good way of being defensive against Charon's
     deduplication bugs.
  *)
  let fun_base_counts =
    FunDeclId.Map.fold
      (fun _ (f : fun_decl) acc ->
        match f.src with
        | TargetDependentItem _ -> acc
        | _ -> add_name acc f.item_meta.name)
      crate.fun_decls NameMap.empty
  in
  let fun_decls =
    FunDeclId.Map.map
      (fun (f : fun_decl) ->
        match f.src with
        | TargetDependentItem _ -> f
        | _ ->
            let name = get_name fun_base_counts f.item_meta.name in
            { f with item_meta = { f.item_meta with name } })
      crate.fun_decls
  in
  (* --- Types: strip PeTarget when the base name is unique --- *)
  let type_base_counts =
    TypeDeclId.Map.fold
      (fun _ (td : type_decl) acc -> add_name acc td.item_meta.name)
      crate.type_decls NameMap.empty
  in
  let type_decls =
    TypeDeclId.Map.map
      (fun (td : type_decl) ->
        let name = get_name type_base_counts td.item_meta.name in
        { td with item_meta = { td.item_meta with name } })
      crate.type_decls
  in
  { crate with fun_decls; type_decls }

(** Remove all occurrences of certain compiler-internal marker traits.

    These traits have no semantic content relevant to verification:
    - [Sized], [MetaSized], [PointeeSized]: type size plumbing
    - [Destruct]: carries drop information
    - [Pointee], [Thin]: pointer metadata plumbing
    - [Send], [Sync]: thread-safety markers
    - [Unpin]: pin-projection marker
    - [Tuple]: identifies tuples for use in the [Fn] family of traits
    - [TrivialClone]: internal marker trait used for some optimizations
    - [Allocator]: unstable API for custom allocators, present on Box/Vec/etc
      but not exposed to stable users

    When we will actually need to reason about these, we will capture their
    semantic content through separation logic predicates.

    We filter out the trait declarations, their impls, their associated items,
    and all references (trait refs, clauses, type constraints, parent clauses).
*)
let filter_marker_traits (crate : crate) : crate =
  let mctx = NameMatcher.ctx_from_crate crate in
  let pats =
    List.map NameMatcher.parse_pattern
      [
        "core::marker::Sized";
        "core::marker::MetaSized";
        "core::marker::PointeeSized";
        "core::marker::Destruct";
        "core::ptr::metadata::Pointee";
        "core::ptr::metadata::Thin";
        "core::marker::Send";
        "core::marker::Sync";
        "core::marker::Unpin";
        "core::marker::Tuple";
        "core::clone::TrivialClone";
        "core::alloc::Allocator";
      ]
  in
  let match_config =
    {
      NameMatcher.map_vars_to_vars = true;
      match_with_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
    }
  in
  (* Collect the trait decl ids to filter *)
  let filtered_ids =
    TraitDeclId.Map.fold
      (fun id (decl : trait_decl) acc ->
        if
          List.exists
            (fun pat ->
              NameMatcher.match_name mctx match_config pat decl.item_meta.name)
            pats
        then TraitDeclId.Set.add id acc
        else acc)
      crate.trait_decls TraitDeclId.Set.empty
  in
  if TraitDeclId.Set.is_empty filtered_ids then crate
  else
    let is_filtered_id id = TraitDeclId.Set.mem id filtered_ids in
    let is_filtered_ref (tr : trait_ref) : bool =
      is_filtered_id tr.trait_decl_ref.binder_value.id
    in
    let is_filtered_clause (clause : trait_param) : bool =
      is_filtered_id clause.trait.binder_value.id
    in
    let check_not_filtered_type_constraint
        (c : trait_type_constraint region_binder) : unit =
      if is_filtered_id c.binder_value.trait_ref.trait_decl_ref.binder_value.id
      then
        let span = c.binder_value.trait_ref.trait_decl_ref.binder_value in
        [%craise_opt_span] None
          ("Unexpected trait type constraint referencing a filtered marker \
            trait (id: "
          ^ TraitDeclId.to_string span.id
          ^ ")")
    in
    (* Remove the trait decls and their impls from declarations and maps *)
    let filtered_impl_ids =
      TraitImplId.Map.fold
        (fun id (impl : trait_impl) acc ->
          if is_filtered_id impl.impl_trait.id then TraitImplId.Set.add id acc
          else acc)
        crate.trait_impls TraitImplId.Set.empty
    in
    let item_source_is_filtered (src : item_source) : bool =
      match src with
      | TraitDeclItem (trait_ref, _) -> is_filtered_id trait_ref.id
      | TraitImplItem (impl_ref, trait_ref, _, _) ->
          TraitImplId.Set.mem impl_ref.id filtered_impl_ids
          || is_filtered_id trait_ref.id
      | _ -> false
    in
    let filtered_global_ids =
      GlobalDeclId.Map.fold
        (fun id (decl : global_decl) acc ->
          if item_source_is_filtered decl.src then GlobalDeclId.Set.add id acc
          else acc)
        crate.global_decls GlobalDeclId.Set.empty
    in
    let filtered_fun_ids =
      FunDeclId.Map.fold
        (fun id (decl : fun_decl) acc ->
          let init_is_filtered =
            match decl.is_global_initializer with
            | None -> false
            | Some id -> GlobalDeclId.Set.mem id filtered_global_ids
          in
          if item_source_is_filtered decl.src || init_is_filtered then
            FunDeclId.Set.add id acc
          else acc)
        crate.fun_decls FunDeclId.Set.empty
    in
    let declarations =
      List.filter_map
        (fun (g : declaration_group) ->
          match g with
          | TraitDeclGroup (NonRecGroup id) ->
              if is_filtered_id id then None else Some g
          | TraitDeclGroup (RecGroup ids) ->
              let ids = List.filter (fun id -> not (is_filtered_id id)) ids in
              if ids <> [] then Some (TraitDeclGroup (RecGroup ids)) else None
          | TraitImplGroup (NonRecGroup id) ->
              if TraitImplId.Set.mem id filtered_impl_ids then None else Some g
          | TraitImplGroup (RecGroup ids) ->
              let ids =
                List.filter
                  (fun id -> not (TraitImplId.Set.mem id filtered_impl_ids))
                  ids
              in
              if ids <> [] then Some (TraitImplGroup (RecGroup ids)) else None
          | FunGroup (NonRecGroup id) ->
              if FunDeclId.Set.mem id filtered_fun_ids then None else Some g
          | FunGroup (RecGroup ids) ->
              let ids =
                List.filter
                  (fun id -> not (FunDeclId.Set.mem id filtered_fun_ids))
                  ids
              in
              if ids <> [] then Some (FunGroup (RecGroup ids)) else None
          | GlobalGroup (NonRecGroup id) ->
              if GlobalDeclId.Set.mem id filtered_global_ids then None
              else Some g
          | GlobalGroup (RecGroup ids) ->
              let ids =
                List.filter
                  (fun id -> not (GlobalDeclId.Set.mem id filtered_global_ids))
                  ids
              in
              if ids <> [] then Some (GlobalGroup (RecGroup ids)) else None
          | MixedGroup g -> (
              let is_filtered_item (id : item_id) =
                match id with
                | IdFun id -> FunDeclId.Set.mem id filtered_fun_ids
                | IdGlobal id -> GlobalDeclId.Set.mem id filtered_global_ids
                | IdTraitDecl id -> is_filtered_id id
                | IdTraitImpl id -> TraitImplId.Set.mem id filtered_impl_ids
                | _ -> false
              in
              match g with
              | NonRecGroup id ->
                  if is_filtered_item id then None else Some (MixedGroup g)
              | RecGroup ids ->
                  let ids =
                    List.filter (fun id -> not (is_filtered_item id)) ids
                  in
                  if ids <> [] then Some (MixedGroup (RecGroup ids)) else None)
          | _ -> Some g)
        crate.declarations
    in
    let trait_decls =
      TraitDeclId.Map.filter
        (fun id _ -> not (is_filtered_id id))
        crate.trait_decls
    in
    let trait_impls =
      TraitImplId.Map.filter
        (fun id _ -> not (TraitImplId.Set.mem id filtered_impl_ids))
        crate.trait_impls
    in
    let global_decls =
      GlobalDeclId.Map.filter
        (fun id _ -> not (GlobalDeclId.Set.mem id filtered_global_ids))
        crate.global_decls
    in
    let fun_decls =
      FunDeclId.Map.filter
        (fun id _ -> not (FunDeclId.Set.mem id filtered_fun_ids))
        crate.fun_decls
    in
    let crate =
      {
        crate with
        declarations;
        trait_decls;
        trait_impls;
        global_decls;
        fun_decls;
      }
    in
    let visitor =
      object (self)
        inherit [_] map_crate as super

        method! visit_generic_args env (args : generic_args) =
          let args = super#visit_generic_args env args in
          {
            args with
            trait_refs =
              List.filter (fun tr -> not (is_filtered_ref tr)) args.trait_refs;
          }

        method! visit_generic_params env (params : generic_params) =
          let params = super#visit_generic_params env params in
          List.iter check_not_filtered_type_constraint
            params.trait_type_constraints;
          {
            params with
            trait_clauses =
              List.filter
                (fun c -> not (is_filtered_clause c))
                params.trait_clauses;
          }

        method! visit_trait_ref_kind env (kind : trait_ref_kind) =
          match kind with
          | BuiltinOrAuto (data, parent_refs, types) ->
              let parent_refs =
                List.filter (fun tr -> not (is_filtered_ref tr)) parent_refs
              in
              let parent_refs =
                List.map (self#visit_trait_ref env) parent_refs
              in
              let types =
                AssocTypeId.Map.map
                  (fun t -> self#visit_trait_assoc_ty_impl env t)
                  types
              in
              BuiltinOrAuto (data, parent_refs, types)
          | _ -> super#visit_trait_ref_kind env kind

        method! visit_trait_decl env (decl : trait_decl) =
          let decl = super#visit_trait_decl env decl in
          {
            decl with
            implied_clauses =
              List.filter
                (fun c -> not (is_filtered_clause c))
                decl.implied_clauses;
          }

        method! visit_trait_impl env (impl_ : trait_impl) =
          let impl_ = super#visit_trait_impl env impl_ in
          {
            impl_ with
            implied_trait_refs =
              List.filter
                (fun tr -> not (is_filtered_ref tr))
                impl_.implied_trait_refs;
          }
      end
    in
    visitor#visit_crate () crate

(* Remove the type aliases from the type declarations and declaration groups *)
let filter_type_aliases (crate : crate) : crate =
  let type_decl_is_alias (ty : type_decl) =
    match ty.kind with
    | Alias _ -> true
    | _ -> false
  in
  (* Whether the declaration group has a single entry that is a type alias.
     Type aliases should not be in recursive groups so we also ensure this doesn't
     happen. *)
  let decl_group_is_single_alias = function
    | TypeGroup (NonRecGroup id) ->
        type_decl_is_alias (TypeDeclId.Map.find id crate.type_decls)
    | TypeGroup (RecGroup ids) ->
        List.iter
          (fun id ->
            let ty = TypeDeclId.Map.find id crate.type_decls in
            if type_decl_is_alias ty then
              [%craise] ty.item_meta.span
                "found a type alias within a recursive group; this is \
                 unexpected")
          ids;
        false
    | _ -> false
  in
  {
    crate with
    type_decls =
      TypeDeclId.Map.filter
        (fun _id ty -> not (type_decl_is_alias ty))
        crate.type_decls;
    declarations =
      List.filter
        (fun decl -> not (decl_group_is_single_alias decl))
        crate.declarations;
  }

(** Whenever we write a string literal in Rust, rustc actually introduces a
    constant of type [&str]. Generally speaking, because [str] is unsized, it
    doesn't make sense to manipulate values of type [str] directly. But in the
    context of Aeneas, it is reasonable to decompose those literals into: a
    string stored in a local variable, then a borrow of this variable.

    Remark: the new statements all have the id 0: this pass requires to refresh
    the ids later. *)
let decompose_str_borrows (_ : crate) (f : fun_decl) : fun_decl =
  (* Map  *)
  let body =
    match f.body with
    | StructuredBody body ->
        let new_locals = ref [] in
        let _, gen =
          LocalId.mk_stateful_generator_starting_at_id
            (LocalId.of_int (List.length body.locals.locals))
        in
        let fresh_local ty =
          let local =
            {
              index = gen ();
              local_ty = ty;
              name = None;
              span = f.item_meta.span;
            }
          in
          new_locals := local :: !new_locals;
          local.index
        in

        (* Function to decompose a constant literal *)
        let decompose_rvalue (span : Meta.span) (lv : place) (rv : rvalue) :
            statement list =
          let new_statements = ref [] in

          (* Visit the rvalue *)
          let visitor =
            object
              inherit [_] map_statement as super

              (* We have to visit all the constant operands.
                 As we might need to replace them with borrows, while borrows
                 are rvalues (i.e., not operands) we have to introduce two
                 intermediate statements: the string initialization, then
                 the borrow, that we can finally move.
              *)
              method! visit_Constant env (cv : constant_expr) =
                match (cv.kind, cv.ty) with
                | ( CLiteral (VStr str),
                    TRef
                      (_, (TAdt { id = TBuiltin TStr; _ } as str_ty), ref_kind)
                  ) ->
                    (* We need to introduce intermediate assignments *)
                    (* First the string initialization *)
                    let local_id =
                      let local_id = fresh_local str_ty in
                      let new_cv : constant_expr =
                        { kind = CLiteral (VStr str); ty = str_ty }
                      in
                      let st =
                        {
                          span;
                          statement_id = StatementId.zero;
                          kind =
                            Assign
                              ( { kind = PlaceLocal local_id; ty = str_ty },
                                Use (Constant new_cv, NoRetag) );
                          comments_before = [];
                        }
                      in
                      new_statements := st :: !new_statements;
                      local_id
                    in
                    let str_len =
                      Constant
                        {
                          kind =
                            CLiteral
                              (VScalar
                                 (UnsignedScalar
                                    (Usize, Z.of_int (String.length str))));
                          ty = TLiteral (TUInt Usize);
                        }
                    in
                    (* Then the borrow *)
                    let local_id =
                      let nlocal_id = fresh_local cv.ty in
                      let bkind =
                        match ref_kind with
                        | RMut -> BMut
                        | RShared -> BShared
                      in
                      let rv =
                        RvRef
                          ( { kind = PlaceLocal local_id; ty = str_ty },
                            bkind,
                            str_len )
                      in
                      let lv = { kind = PlaceLocal nlocal_id; ty = cv.ty } in
                      let st =
                        {
                          span;
                          statement_id = StatementId.zero;
                          kind = Assign (lv, rv);
                          comments_before = [];
                        }
                      in
                      new_statements := st :: !new_statements;
                      nlocal_id
                    in
                    (* Finally we can move the value *)
                    Move { kind = PlaceLocal local_id; ty = cv.ty }
                | _ -> super#visit_Constant env cv
            end
          in

          let rv = visitor#visit_rvalue () rv in

          (* Construct the sequence *)
          let assign =
            {
              span;
              statement_id = StatementId.zero;
              kind = Assign (lv, rv);
              comments_before = [];
            }
          in
          (* Note that the new statements are in reverse order *)
          let statements = assign :: !new_statements in
          List.rev statements
        in

        (* Visit all the statements and decompose the literals *)
        let decompose_in_statement (st : statement) : statement list =
          match st.kind with
          | Assign (lv, rv) -> decompose_rvalue st.span lv rv
          | _ -> [ st ]
        in
        let body_body = map_statement decompose_in_statement body.body in
        StructuredBody
          {
            body with
            body = body_body;
            locals =
              {
                body.locals with
                locals = body.locals.locals @ List.rev !new_locals;
              };
          }
    | other -> other
  in
  { f with body }

(** Refresh the statement ids to make sure they are unique *)
let refresh_statement_ids (_ : crate) (f : fun_decl) : fun_decl =
  (* Map  *)
  let body =
    match f.body with
    | StructuredBody body ->
        let _, gen_id = StatementId.fresh_stateful_generator () in

        (* Visit the rvalue *)
        let visitor =
          object
            inherit [_] map_statement
            method! visit_statement_id _ _ = gen_id ()
          end
        in

        StructuredBody { body with body = visitor#visit_block () body.body }
    | other -> other
  in
  { f with body }

(** We simplify statements of the shape:
    {[
      x := from_str<'_>(const ("Error"));
      StorageDead ...;
      panic(core::panicking::panic_fmt)

        ~>

      panic(core::panicking::panic_fmt)
    ]}

    TODO: remove *)
let simplify_panics (crate : crate) (f : fun_decl) : fun_decl =
  let pats =
    [
      "core::fmt::{core::fmt::Arguments<'a>}::from_str";
      "core::fmt::{core::fmt::Arguments<'a>}::from_str_nonconst";
    ]
  in
  let pats = List.map (fun p -> (NameMatcher.parse_pattern p, ())) pats in
  (* TODO: we shouldn't need to use a names map *)
  let names_map = NameMatcher.NameMatcherMap.of_list pats in
  let match_ctx = Charon.NameMatcher.ctx_from_crate crate in
  let is_from_str (d : fun_decl) =
    let config = ExtractName.default_match_config in
    NameMatcher.NameMatcherMap.mem match_ctx config d.item_meta.name names_map
  in

  let visitor =
    object (self)
      inherit [_] map_statement

      method! visit_block env (block : block) =
        let is_from_str_call (st : statement) : bool =
          match st.kind with
          | Call
              ({ func = FnOpRegular { kind = FunId (FRegular fid); _ }; _ }, _)
            -> (
              match FunDeclId.Map.find_opt fid crate.fun_decls with
              | Some decl -> is_from_str decl
              | None -> false)
          | _ -> false
        in

        let rec skip_storage_dead (stl : statement list) : statement list =
          match stl with
          | st :: stl -> (
              match st.kind with
              | StorageDead _ -> skip_storage_dead stl
              | _ -> st :: stl)
          | [] -> []
        in

        let rec update (stl : statement list) : statement list =
          match stl with
          | [] -> []
          | st0 :: stl when is_from_str_call st0 -> (
              match skip_storage_dead stl with
              | st1 :: stl1 -> (
                  match st1.kind with
                  | Abort (Panic _) ->
                      self#visit_statement env st1 :: update stl1
                  | _ -> self#visit_statement env st0 :: update stl)
              | [] -> self#visit_statement env st0 :: update stl)
          | st0 :: stl -> self#visit_statement env st0 :: update stl
        in
        { block with statements = update block.statements }
    end
  in

  let body =
    match f.body with
    | StructuredBody body ->
        StructuredBody { body with body = visitor#visit_block () body.body }
    | other -> other
  in
  { f with body }

(** This micro-pass introduces intermediate assignments to access the global
    values in order to simplify the semantics.

    Whenever we access a constant, we introduce a shared borrow and a
    dereference. Ex.:

    {[
      let x = copy C;

        ~~>

      let tmp = &C;
      let x = copy *C;
    ]}

    Remark: we use the crate to lookup the type of the globals.

    TODO: generalize the evaluation of globals in the symbolic interpreter. *)
let decompose_global_accesses (crate : crate) (f : fun_decl) : fun_decl =
  (* Map  *)
  let body =
    match f.body with
    | StructuredBody body -> (
        let new_locals = ref [] in
        let _, gen =
          LocalId.mk_stateful_generator_starting_at_id
            (LocalId.of_int (List.length body.locals.locals))
        in
        let fresh_local ty =
          let local =
            {
              index = gen ();
              local_ty = ty;
              name = None;
              span = f.item_meta.span;
            }
          in
          new_locals := local :: !new_locals;
          local.index
        in

        (* Function to decompose the operands in a statement *)
        let decompose_in_statement (st : statement) : statement list =
          let span = st.span in
          let new_statements = ref [] in

          (* Visit the rvalue *)
          let visitor =
            object
              inherit [_] map_statement as super
              method! visit_place _ p = super#visit_place p.ty p

              method! visit_PlaceGlobal ty gref =
                (* Compute the type of the reference *)
                let ref_ty = TRef (RErased, ty, RShared) in

                (* Introduce the intermediate reference *)
                let local_id =
                  let local_id = fresh_local ref_ty in
                  let metadata = Constant mk_unit_const in
                  let st =
                    {
                      span;
                      statement_id = StatementId.zero;
                      kind =
                        Assign
                          ( { kind = PlaceLocal local_id; ty = ref_ty },
                            RvRef
                              ( { kind = PlaceGlobal gref; ty },
                                BShared,
                                metadata ) );
                      comments_before = [];
                    }
                  in
                  new_statements := st :: !new_statements;
                  local_id
                in

                (* Finally we can update the place *)
                PlaceProjection
                  ({ kind = PlaceLocal local_id; ty = ref_ty }, Deref)
            end
          in

          let kind =
            match st.kind with
            | Assign (lv, rv) -> Assign (lv, visitor#visit_rvalue mk_unit_ty rv)
            | Assert ({ cond; expected; check_kind }, on_failure, on_unwind) ->
                let cond = visitor#visit_operand mk_unit_ty cond in
                Assert ({ cond; expected; check_kind }, on_failure, on_unwind)
            | Call ({ func; args; dest }, on_unwind) ->
                let func = visitor#visit_fn_operand mk_unit_ty func in
                let args = List.map (visitor#visit_operand mk_unit_ty) args in
                Call ({ func; args; dest }, on_unwind)
            | Switch (If (cond, yes, no)) ->
                Switch (If (visitor#visit_operand mk_unit_ty cond, yes, no))
            | Switch (SwitchInt (op, ty, branches, otherwise)) ->
                Switch (SwitchInt
                  (visitor#visit_operand mk_unit_ty op, ty, branches, otherwise))
            | Switch (Match (scrut, branches, otherwise)) ->
                Switch (Match
                  (visitor#visit_place mk_unit_ty scrut, branches, otherwise))
            | SetDiscriminant _ | StorageLive _ | StorageDead _ | PlaceMention _
            | Drop (_, _, _, _)
            | Abort _
            | Return
            | UnwindResume
            | Break _
            | Continue _
            | Nop
            | Loop _
            | Error _ -> st.kind
            | _ ->
                [%craise] st.span
                  ("unsupported statement: " ^ show_statement_kind st.kind)
          in
          let st = { st with kind } in

          List.rev (st :: !new_statements)
        in

        (* Visit all the statements and decompose the operands *)
        try
          let body_body = map_statement decompose_in_statement body.body in
          StructuredBody
            {
              body with
              body = body_body;
              locals =
                {
                  body.locals with
                  locals = body.locals.locals @ List.rev !new_locals;
                };
            }
        with CFailure error ->
          let mctx = Charon.NameMatcher.ctx_from_crate crate in
          let fmt_env = Print.crate_to_fmt_env crate in
          let name = Print.name_to_string fmt_env f.item_meta.name in
          let name_pattern =
            try
              let c : Charon.NameMatcher.to_pat_config =
                {
                  tgt = TkPattern;
                  use_trait_decl_refs = ExtractName.match_with_trait_decl_refs;
                }
              in
              let pat =
                LlbcAstUtils.name_to_pattern (Some f.item_meta.span) mctx c
                  f.item_meta.name
              in
              Charon.NameMatcher.pattern_to_string { tgt = TkPattern } pat
            with CFailure _ ->
              "(could not compute the name pattern due to a different error)"
          in
          [%save_error_opt_span] error.span
            ("Failure when pre- processing: " ^ name
           ^ "; ignoring its body.\nName pattern: '" ^ name_pattern ^ "'");
          OpaqueBody)
    | other -> other
  in
  { f with body }

(** We do not support static regions yet.

    In order to support some printing functions, for now we update their
    signature to replace ['static] with a region variable. This should be fine
    as a temporary measure as we can pretend these functions copy the input
    string they receive (the static references are references to strings).

    TODO: remove once https://github.com/AeneasVerif/aeneas/issues/727 is fixed
*)
let replace_static (crate : crate) : crate =
  (* We update the uses of: [core::fmt::{core::fmt::Arguments<'a>}::from_str] *)
  let pat =
    NameMatcher.parse_pattern "core::fmt::{core::fmt::Arguments<'a>}::from_str"
  in

  (* Find the function [core::fmt::{core::fmt::Arguments<'a>}::from_str]:
     - we want to update its signature to replace 'static with a lifetime variable
     - we want to update its uses
  *)
  let names_set = NameMatcher.NameMatcherMap.of_list [ (pat, ()) ] in
  let match_ctx = Charon.NameMatcher.ctx_from_crate crate in
  let in_set (d : fun_decl) : bool =
    let config = ExtractName.default_match_config in
    NameMatcher.NameMatcherMap.mem match_ctx config d.item_meta.name names_set
  in
  let decl_opt = ref None in
  let in_set (_ : FunDeclId.id) (d : fun_decl) =
    if in_set d then (
      decl_opt := Some d;
      true)
    else false
  in

  if not (FunDeclId.Map.exists in_set crate.fun_decls) then crate
  else (* The function [from_str] is used in the crate *)
    let d = Option.get !decl_opt in

    (* Update the signature *)
    let generics =
      {
        d.generics with
        regions =
          d.generics.regions
          @ [
              {
                index = RegionId.of_int 1;
                name = Some "'b";
                mutability = LtUnknown;
              };
            ];
      }
    in
    let signature =
      let visitor =
        object
          inherit [_] map_ty
          method! visit_RStatic _ = RVar (Free (RegionId.of_int 1))
        end
      in
      visitor#visit_fun_sig () d.signature
    in

    let d = { d with generics; signature } in
    [%ltrace
      let env = Print.crate_to_fmt_env crate in
      "Updated declaration:\n" ^ Print.fun_decl_to_string env "" " " d];
    let crate =
      { crate with fun_decls = FunDeclId.Map.add d.def_id d crate.fun_decls }
    in

    (* Update the uses of this definition *)
    let update (f : fun_decl) : fun_decl =
      match f.body with
      | StructuredBody body ->
          let visitor =
            object
              inherit [_] map_statement

              method! visit_Call _ call on_unwind =
                match call.func with
                | FnOpRegular { kind = FunId (FRegular id) as kind; generics }
                  when id = d.def_id ->
                    let func =
                      FnOpRegular
                        {
                          kind;
                          generics =
                            {
                              generics with
                              regions = generics.regions @ [ RErased ];
                            };
                        }
                    in
                    Call ({ call with func }, on_unwind)
                | _ -> Call (call, on_unwind)
            end
          in

          let body = { body with body = visitor#visit_block () body.body } in
          { f with body = StructuredBody body }
      | _ -> f
    in
    let fun_decls = FunDeclId.Map.map update crate.fun_decls in
    { crate with fun_decls }

(** Charon introduces vtables for the traits which support dyn. We do not want
    to translate the corresponding type and global declarations. Moreover, the
    presence of those declarations leads to mutually recursive groups of traits
    and types. This micro-pass filters these definitions. *)
let remove_vtables (crate : crate) : crate =
  let src_is_vtable (src : item_source) : bool =
    match src with
    | VTableInstanceItem _ | VTableTyItem _ | VTableMethodShimItem -> true
    | _ -> false
  in

  (* Filter the groups.

     We detect mixed groups which combine trait declarations and their corresponding
     vtable types, and remove the vtable types (and convert the group to a homogeneous
     group if possible). We also filter the globals (and the functions corresponding
     to their implementation) introduced for the vtables.
  *)
  let declarations =
    List.filter_map
      (fun (g : declaration_group) ->
        match g with
        | GlobalGroup g -> (
            (* Filter the vtables *)
            let keep (id : global_decl_id) : bool =
              match GlobalDeclId.Map.find_opt id crate.global_decls with
              | None -> true
              | Some d -> not (src_is_vtable d.src)
            in
            match g with
            | RecGroup ids ->
                let ids = List.filter keep ids in
                if ids <> [] then Some (GlobalGroup (RecGroup ids)) else None
            | NonRecGroup id ->
                if keep id then Some (GlobalGroup (NonRecGroup id)) else None)
        | FunGroup g -> (
            (* Filter the vtables *)
            let keep (id : fun_decl_id) : bool =
              match FunDeclId.Map.find_opt id crate.fun_decls with
              | None -> true
              | Some d -> not (src_is_vtable d.src)
            in
            match g with
            | RecGroup ids ->
                let ids = List.filter keep ids in
                if ids <> [] then Some (FunGroup (RecGroup ids)) else None
            | NonRecGroup id ->
                if keep id then Some (FunGroup (NonRecGroup id)) else None)
        | TypeGroup g -> (
            (* Filter the vtables *)
            let keep (id : type_decl_id) : bool =
              match TypeDeclId.Map.find_opt id crate.type_decls with
              | None -> true
              | Some d -> not (src_is_vtable d.src)
            in
            match g with
            | RecGroup ids ->
                let ids = List.filter keep ids in
                if ids <> [] then Some (TypeGroup (RecGroup ids)) else None
            | NonRecGroup id ->
                if keep id then Some (TypeGroup (NonRecGroup id)) else None)
        | MixedGroup g -> (
            (* If the group is a mutually recursive group, filter the vtable types
               and check if the resulting group is only made of trait declarations.

               TODO: we should check whether the resulting group is recursive or not.
            *)
            match g with
            | RecGroup ids ->
                let keep (id : type_decl_id) : bool =
                  match TypeDeclId.Map.find_opt id crate.type_decls with
                  | None -> true
                  | Some d -> not (src_is_vtable d.src)
                in
                let ids =
                  List.filter
                    (fun (id : item_id) ->
                      match id with
                      | IdType id -> keep id
                      | _ -> true)
                    ids
                in
                (* Note that the resulting group shouldn't be empty, but we can
                   still support this case *)
                if ids = [] then None
                else if
                  List.for_all
                    (fun (id : item_id) ->
                      match id with
                      | IdTraitDecl _ -> true
                      | _ -> false)
                    ids
                then
                  (* There only remains trait ids *)
                  let ids =
                    List.map
                      (fun (id : item_id) ->
                        match id with
                        | IdTraitDecl id -> id
                        | _ -> raise (Failure "Unreachable"))
                      ids
                  in
                  (* If the resulting group is a singleton, check whether
                     it is recursive *)
                  match ids with
                  | [ id ] ->
                      let is_rec =
                        match TraitDeclId.Map.find_opt id crate.trait_decls with
                        | None ->
                            (* don't know so by default we consider it to be recursive *)
                            true
                        | Some d ->
                            (* We count the number of occurrences of the id of the trait
                             decl itself - if it's > 1 then it means it is recursive
                             (there is one occurrence for the [def_id] field) *)
                            let found = ref 0 in
                            let visitor =
                              object (self)
                                inherit [_] iter_trait_decl

                                method! visit_trait_ref_contents _
                                    { kind; trait_decl_ref = _ } =
                                  (* We ignore the [trait_decl_ref] which refer
                                     to the trait declaration itself if this is
                                     an occurrence of [Self] *)
                                  self#visit_trait_ref_kind () kind

                                method! visit_trait_decl_id _ id' =
                                  if id' = id then found := !found + 1
                              end
                            in
                            visitor#visit_trait_decl () { d with vtable = None };
                            !found > 1
                      in
                      if is_rec then Some (TraitDeclGroup (RecGroup [ id ]))
                      else Some (TraitDeclGroup (NonRecGroup id))
                  | _ -> Some (TraitDeclGroup (RecGroup ids))
                else Some (MixedGroup (RecGroup ids))
            | _ -> Some (MixedGroup g))
        | _ -> Some g)
      crate.declarations
  in

  (* *)
  let type_decls =
    TypeDeclId.Map.filter
      (fun _ (d : type_decl) -> not (src_is_vtable d.src))
      crate.type_decls
  in

  let global_decls =
    GlobalDeclId.Map.filter
      (fun _ (d : global_decl) -> not (src_is_vtable d.src))
      crate.global_decls
  in

  let fun_decls =
    FunDeclId.Map.filter
      (fun _ (d : fun_decl) -> not (src_is_vtable d.src))
      crate.fun_decls
  in

  let trait_decls =
    TraitDeclId.Map.map
      (fun (d : trait_decl) ->
        (* Remove the vtable *)
        { d with vtable = None })
      crate.trait_decls
  in

  { crate with declarations; type_decls; global_decls; fun_decls; trait_decls }

let name_is_valid (n : string) : bool =
  let is_valid_char c =
    (c >= 'a' && c <= 'z')
    || (c >= 'A' && c <= 'Z')
    || (c >= '0' && c <= '9')
    || c = '_'
  in
  String.for_all is_valid_char n

(** The basename introduced by Charon for impl types (see
    https://github.com/AeneasVerif/charon/issues/1013) is an invalid name: we
    detect this case here and use a valid name instead. As it only happens for
    inputs of type `impl Trait` we use `Impl` as a basename. *)
let rename_type_vars (crate : crate) : crate =
  let visitor =
    object
      inherit [_] map_crate as super

      method! visit_generic_params env generics =
        (* Explore the types and rename them *)
        let num_renames =
          List.length
            (List.filter
               (fun (p : type_param) -> not (name_is_valid p.name))
               generics.types)
        in
        let rename =
          if num_renames > 1 then (
            let index = ref 0 in
            fun () ->
              let i = !index in
              index := !index + 1;
              "Impl" ^ string_of_int i)
          else fun () -> "Impl"
        in
        let types =
          List.map
            (fun (p : type_param) ->
              let name = if name_is_valid p.name then p.name else rename () in
              { p with name })
            generics.types
        in
        super#visit_generic_params env { generics with types }
    end
  in
  visitor#visit_crate () crate

(** Simplify calls to:
    - the blanket [IntoIterator::into_iter] implementation (we replace it with
      an assignment)
    - the blanket [TryInto::try_into] implementation (we replace it with a call
      to the [try_from] method of the required [TryFrom] clause)

    TODO: remove once we have partial monomorphization *)
let simplify_trait_calls (crate : crate) : crate =
  (* Create a map from pattern to method *)
  (* Blanket definition for [into_iter] *)
  let into_iter_pat =
    NameMatcher.parse_pattern
      "core::iter::traits::collect::{core::iter::traits::collect::IntoIterator<@I, \
       @Item, @I>}::into_iter"
  in
  (* Blanket definition for [try_into] *)
  let try_into_pat =
    NameMatcher.parse_pattern
      "core::convert::{core::convert::TryInto<@T, @U, @Error>}::try_into"
  in
  let mctx = NameMatcher.ctx_from_crate crate in
  let match_pattern =
    NameMatcher.match_name mctx
      {
        map_vars_to_vars = true;
        match_with_trait_decl_refs = Config.match_patterns_with_trait_decl_refs;
      }
  in
  let is_blanket_into_iter = match_pattern into_iter_pat in
  let is_blanket_try_into = match_pattern try_into_pat in

  let try_replace_call (super_visit : unit -> statement_kind) (span : Meta.span)
      (call : call) (on_unwind : block) : statement_kind =
    match call.func with
    | FnOpRegular { kind = FunId (FRegular fid); generics } -> (
        match FunDeclId.Map.find_opt fid crate.fun_decls with
        | Some d
          when List.length generics.trait_refs > 0 && List.length call.args > 0
          ->
            if is_blanket_into_iter d.item_meta.name then (
              (* Replace the call by an assignment *)
              [%sanity_check] span (List.length call.args = 1);
              let arg = Use (List.hd call.args, NoRetag) in
              Assign (call.dest, arg))
            else if is_blanket_try_into d.item_meta.name then (
              [%ldebug
                "- call: " ^ call_to_string crate call ^ "\n- generics: "
                ^ generic_args_to_string crate generics];
              (* There should be a single trait ref implementing [TryFrom] *)
              match generics.trait_refs with
              | [ trait_ref ] -> (
                  (* There are two cases depending on whether this is an impl or not *)
                  match trait_ref.kind with
                  | TraitImpl { id = impl_id; generics = impl_generics } ->
                      (* Lookup the impl to retrieve the method id *)
                      let impl =
                        [%unwrap_with_span] span
                          (TraitImplId.Map.find_opt impl_id crate.trait_impls)
                          "Internal error"
                      in
                      (* The TryFrom trait has a single method (try_from) *)
                      let method_ref =
                        [%unwrap_with_span] span
                          (List.nth_opt
                             (TraitMethodId.Map.values impl.methods)
                             0)
                          "Internal error"
                      in

                      [%sanity_check] span
                        (method_ref.binder_params = empty_generic_params);

                      [%ldebug
                        "- call: " ^ call_to_string crate call
                        ^ "\n- generics: "
                        ^ generic_args_to_string crate generics
                        ^ "\n- impl.generic_params: "
                        ^ generic_params_to_string crate impl.generics
                        ^ "\n- impl_generics: "
                        ^ generic_args_to_string crate impl_generics
                        ^ "\n- method_ref.binder_params: "
                        ^ generic_params_to_string crate
                            method_ref.binder_params
                        ^ "\n- method_ref.binder_value: "
                        ^ fun_decl_ref_to_string crate method_ref.binder_value
                        ^ "\n "];

                      (* Instantiate *)
                      let subst =
                        [%add_loc] Substitute.make_subst_from_generics
                          (Some span) impl.generics impl_generics
                          (UnknownTrait "UNREACHABLE")
                      in
                      let generics =
                        Substitute.generic_args_substitute subst
                          method_ref.binder_value.generics
                      in

                      (* *)
                      let kind = FunId (FRegular method_ref.binder_value.id) in
                      let func = FnOpRegular { kind; generics } in
                      Call ({ call with func }, on_unwind)
                  | _ ->
                      (* TODO: *)
                      super_visit ())
              | _ -> [%internal_error] span)
            else super_visit ()
        | _ -> super_visit ())
    | _ -> super_visit ()
  in

  (* The map visitor to simplify the calls *)
  let visitor =
    object
      inherit [_] map_crate as super

      (* Keep track of the last span *)
      method! visit_statement _ st = super#visit_statement (Some st.span) st

      method! visit_Call span call on_unwind =
        try_replace_call
          (fun _ -> super#visit_Call span call on_unwind)
          (Option.get span) call on_unwind
    end
  in
  let crate = visitor#visit_crate None crate in

  (* Re-compute the set of used trait impls and fun declarations: by simplifying
     the calls we may have filtered some annoying ones

     Remark: the way we explore the crate is slightly approximative below.
     We should improve it.
  *)
  let used_impls = ref TraitImplId.Set.empty in
  let impls_to_explore = ref [] in
  let used_funs = ref FunDeclId.Set.empty in

  (* First explore the transparent functions *)
  let visitor =
    object
      inherit [_] iter_statement

      method! visit_trait_impl_id _ id =
        if not (TraitImplId.Set.mem id !used_impls) then (
          used_impls := TraitImplId.Set.add id !used_impls;
          impls_to_explore := id :: !impls_to_explore)

      method! visit_fun_decl_id _ id =
        used_funs := FunDeclId.Set.add id !used_funs
    end
  in
  FunDeclId.Map.iter
    (fun _ (f : fun_decl) ->
      if f.item_meta.is_local || (match f.body with StructuredBody _ -> true | _ -> false) then visitor#visit_fun_decl_id () f.def_id;
      match f.body with
      | StructuredBody body -> visitor#visit_block () body.body
      | _ -> ())
    crate.fun_decls;

  GlobalDeclId.Map.iter
    (fun _ (d : global_decl) -> visitor#visit_constant_expr () d.value)
    crate.global_decls;

  TraitDeclId.Map.iter
    (fun _ (d : trait_decl) ->
      TraitMethodId.Map.iter
        (fun _ (d : trait_method binder) ->
          Option.iter
            (fun (default : fun_decl_ref) ->
              visitor#visit_fun_decl_id () default.id)
            d.binder_value.default)
        d.methods)
    crate.trait_decls;

  (* Add the local trait impls *)
  TraitImplId.Map.iter
    (fun _ (d : trait_impl) ->
      if d.item_meta.is_local then visitor#visit_trait_impl_id () d.def_id)
    crate.trait_impls;

  (* Explore the impls *)
  while !impls_to_explore <> [] do
    let id = List.hd !impls_to_explore in
    impls_to_explore := List.tl !impls_to_explore;
    match TraitImplId.Map.find_opt id crate.trait_impls with
    | None -> ()
    | Some impl ->
        List.iter (visitor#visit_trait_ref ()) impl.implied_trait_refs;
        TraitMethodId.Map.iter
          (fun _ (x : fun_decl_ref binder) ->
            visitor#visit_fun_decl_id () x.binder_value.id)
          impl.methods
  done;

  (* Filter the declaration groups we want to extract *)
  let keep_group (gr : declaration_group) : bool =
    match gr with
    | TraitImplGroup (NonRecGroup id) ->
        if TraitImplId.Set.mem id !used_impls then true else false
    | TraitImplGroup (RecGroup ids) ->
        if List.exists (fun id -> TraitImplId.Set.mem id !used_impls) ids then
          true
        else false
    | FunGroup (NonRecGroup id) ->
        if FunDeclId.Set.mem id !used_funs then true else false
    | FunGroup (RecGroup ids) ->
        if List.exists (fun id -> FunDeclId.Set.mem id !used_funs) ids then true
        else false
    | _ -> true
  in
  let declarations = List.filter keep_group crate.declarations in

  (* *)
  { crate with declarations }

(** Add missing outlives constraints for closure trait implementations.

    Charon sometimes fails to properly retrieves the lifetime constraints
    between the inputs and outputs of closures. This passes is a temporary
    (ad-hoc) fix for the following situation:
    {[
      call_mut<'a, 'b, 'c>(v@1 : &'c mut closure<'a>) -> &'b T
    ]}
    that we update to:
    {[
      call_mut<'b, 'c>(v@1 : &'c mut closure<'a>) -> &'a T
    ]}

    Similarly we do:
    {[
      call_once<'a, 'b>(v@1 : mut closure<'a>) -> &'b T
    ]}
    that we update to:
    {[
      call_once<'b, 'c>(v@1 : mut closure<'a>) -> &'a T
    ]}

    See https://github.com/AeneasVerif/aeneas/issues/804 and
    https://github.com/AeneasVerif/charon/issues/1040.

    TODO: remove once the Charon issue is fixed. *)
let fix_closure_lifetimes (crate : crate) (f : fun_decl) : fun_decl =
  (* Check that the function is a closure *)
  (* Decompose the type of the first argument (it should be the state).
     We do the update only if the state is inside a reference. *)
  let find_input_region (ty : ty) =
    match ty with
    | TAdt { id = TAdtId id; generics = { regions = [ RVar rid ]; _ } }
    | TRef
        (_, TAdt { id = TAdtId id; generics = { regions = [ RVar rid ]; _ } }, _)
      -> (
        match TypeDeclId.Map.find_opt id crate.type_decls with
        | Some decl -> (
            match decl.src with
            | ClosureItem _ -> Some rid
            | _ -> None)
        | None -> None)
    | _ -> None
  in
  match f.signature.inputs with
  | [] -> f
  | first_input :: _ -> (
      match (find_input_region first_input, f.signature.output) with
      | Some input_rid, TRef (RVar _, ref_ty, kind) ->
          (* TODO: support more cases for the output? *)
          let output = TRef (RVar input_rid, ref_ty, kind) in
          (* Remark: we don't have to remove the region we substitute from the region
             parameters *)
          let signature = { f.signature with output } in
          let f = { f with signature } in
          [%ltrace
            let env = Print.crate_to_fmt_env crate in
            "Updated: " ^ Print.fun_decl_to_string env "" " " f];
          f
      | _, _ -> f)

let apply_passes (crate : crate) : crate =
  (* Passes that apply to the whole crate *)
  let crate = update_array_default crate in
  (* Passes that apply to individual function bodies *)
  let function_passes =
    [
      ("fix_closure_lifetimes", fix_closure_lifetimes);
      ("erase_body_regions", erase_body_regions);
      ( "eliminate_metadata_only_slice_raw_pointers",
        eliminate_metadata_only_slice_raw_pointers );
      ("remove_unreachable", remove_unreachable);
      ("restore_structured_nested_returns", restore_structured_nested_returns);
      ("lower_nested_loop_returns", lower_nested_loop_returns);
      ("eliminate_outer_loop_control", eliminate_outer_loop_control);
      ("update_loop", update_loops);
      ("remove_useless_joins", remove_useless_joins);
      ( "remove_shallow_borrows_storage_live_dead",
        remove_shallow_borrows_storage_live_dead );
      ("decompose_str_borrows", decompose_str_borrows);
      ("simplify_panics", simplify_panics);
      ("decompose_global_accesses", decompose_global_accesses);
      ("refresh_statement_ids", refresh_statement_ids);
    ]
  in
  (* Attempt to apply a pass: if it fails we replace the body by [None] *)
  let apply_function_pass (pass_name : string)
      (pass : crate -> fun_decl -> fun_decl) (f : fun_decl) =
    try
      let f = pass crate f in
      [%ltrace
        let env = Print.crate_to_fmt_env crate in
        "After applying [" ^ pass_name ^ "]:\n"
        ^ Print.fun_decl_to_string env "" " " f];
      f
    with CFailure e ->
      (* The error was already registered, we don't need to register it twice.
         However, we replace the body of the function, and save an error to
         report to the user the fact that we will ignore the function body *)
      let fmt = Print.crate_to_fmt_env crate in
      let name = Print.name_to_string fmt f.item_meta.name in
      [%save_error] f.item_meta.span
        ("Ignoring the body of '" ^ name ^ "' because of previous error");
      let msg =
        Errors.format_error_message_with_file_line e.file e.line e.span e.msg
      in
      { f with body = ErrorBody { span = f.item_meta.span; msg } }
  in
  let fun_decls : fun_decl FunDeclId.Map.t =
    let num_decls = FunDeclId.Map.cardinal crate.fun_decls in
    ProgressBar.with_reporter num_decls "Applied prepasses: " (fun report ->
        FunDeclId.Map.map
          (fun f ->
            [%ltrace
              let env = Print.crate_to_fmt_env crate in
              "Before applying the prepasses:\n"
              ^ Print.fun_decl_to_string env "" " " f];
            let f : fun_decl =
              List.fold_left
                (fun f (name, pass) -> apply_function_pass name pass f)
                f function_passes
            in
            report 1;
            f)
          crate.fun_decls)
  in
  let crate = { crate with fun_decls } in
  let crate = strip_unnecessary_target_suffixes crate in
  let crate = filter_marker_traits crate in
  let crate = filter_type_aliases crate in
  let crate = replace_static crate in
  let crate = remove_vtables crate in
  let crate = rename_type_vars crate in
  let crate = simplify_trait_calls crate in
  [%ltrace "After pre-passes:\n" ^ Print.crate_to_string crate ^ "\n"];
  crate
