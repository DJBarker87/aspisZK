//! UNVERIFIED candidate. A downstream typed-AST transformation; not a source
//! execution theorem. Never overwrite the original LLBC or pinned toolchain.
mod helper;
use charon_lib::ast::*;
use charon_lib::export::CrateData;
use charon_lib::options::SerializationFormat;
use charon_lib::name_matcher::NamePattern;
use derive_generic_visitor::*;
use index_vec::Idx;
use std::collections::HashMap;
use std::path::Path;
use helper::{Scope, replacement, rewrite, remove_param};

#[derive(Clone)]
struct Plan { slot: TypeVarId, old_types: usize, projection: Ty, scope: Scope }

fn plan(params: &GenericParams, scope: Scope, try_id: TraitDeclId, output: AssocTypeId) -> Option<Plan> {
    if params.trait_type_constraints.is_empty() { return None; }
    // This candidate handles one plain associated-type equality only. It never
    // discards a constraint it cannot transport to a reflexive equality.
    assert_eq!(params.trait_type_constraints.len(), 1, "unsupported constraint set");
    let b = params.trait_type_constraints.iter().next().unwrap();
    assert!(b.regions.is_empty(), "constraint-local lifetime would escape");
    let c = &b.skip_binder;
    assert_eq!(c.trait_ref.trait_decl_ref.skip_binder.id, try_id);
    assert_eq!(c.type_id, output);
    let rhs = c.ty.clone().move_from_under_binder().expect("RHS scope escape");
    let slot = match (scope, rhs.kind()) {
        (Scope::Free, TyKind::TypeVar(DeBruijnVar::Free(id))) => *id,
        (Scope::Bound, TyKind::TypeVar(DeBruijnVar::Bound(depth,id))) if depth.is_zero() => *id,
        _ => panic!("not a type variable in the current binder"),
    };
    assert!(slot.index() < params.types.len());
    let p = TyKind::TraitType(c.trait_ref.clone(), c.type_id, GenericArgs::empty()).into_ty()
        .move_from_under_binder().expect("projection scope escape");
    let p = replacement(p, slot, scope);
    Some(Plan { slot, old_types: params.types.len(), projection: p, scope })
}

fn rewrite_params(params: &mut GenericParams, p: &Plan) {
    rewrite(params, p.slot, p.scope, &p.projection);
    let c = &params.trait_type_constraints.iter().next().unwrap().skip_binder;
    let lhs = TyKind::TraitType(c.trait_ref.clone(), c.type_id, GenericArgs::empty()).into_ty();
    assert_eq!(c.ty, lhs, "substituted equality is not reflexive");
    // Only now is the one equality a tautology. All other predicate vectors stay.
    params.trait_type_constraints.clear();
    remove_param(params, p.slot);
    assert_eq!(params.types.len()+1, p.old_types);
    params.check_consistency();
}

fn remove_arg(g: &mut GenericArgs, slot: TypeVarId, old_types: usize) {
    assert_eq!(g.types.len(), old_types, "unrecognized reference arity");
    g.types = std::mem::take(&mut g.types).into_iter().enumerate()
        .filter_map(|(i,t)| if i==slot.index() {None} else {Some(t)}).collect();
}

#[derive(Visitor)]
struct RewriteRefs {
    functions: HashMap<FunDeclId,Plan>,
    iterator: TraitDeclId,
    method: TraitMethodId,
    method_plan: Plan,
    direct_count: usize,
    dispatch_count: usize,
}
impl VisitAstMut for RewriteRefs {
    fn enter_fun_decl_ref(&mut self, r: &mut FunDeclRef) {
        if let Some(p)=self.functions.get(&r.id) {
            remove_arg(&mut r.generics, p.slot, p.old_types);
            self.direct_count+=1;
        }
    }
    fn enter_fn_ptr(&mut self, r: &mut FnPtr) {
        match &*r.kind {
            FnPtrKind::Fun(FunId::Regular(id)) => if let Some(p)=self.functions.get(id) {
                remove_arg(&mut r.generics,p.slot,p.old_types);
                self.direct_count+=1;
            },
            FnPtrKind::Trait(tr,m) if tr.trait_decl_ref.skip_binder.id==self.iterator && *m==self.method => {
                remove_arg(&mut r.generics,self.method_plan.slot,self.method_plan.old_types);
                self.dispatch_count+=1;
            },
            _ => (),
        }
    }
    fn enter_maybe_builtin_fun_decl_ref(&mut self,r:&mut MaybeBuiltinFunDeclRef) {
        if let FunId::Regular(id)=r.id {
            if let Some(p)=self.functions.get(&id) {
                remove_arg(&mut r.generics,p.slot,p.old_types);
                self.direct_count+=1;
            }
        }
    }
}

fn main() {
    let a:Vec<_>=std::env::args().collect();
    assert_eq!(a.len(),3,"input.llbc output.llbc");
    assert_ne!(Path::new(&a[1]),Path::new(&a[2]));
    assert!(!Path::new(&a[2]).exists(),"output must be new");
    let mut data=CrateData::deserialize_from_file(Path::new(&a[1]),SerializationFormat::Json).unwrap();
    assert!(!data.has_errors);
    let krate=&mut data.translated;
    let resolve=|name:&str| {
        let pattern=NamePattern::parse(name).unwrap();
        let ids:Vec<_>=krate.item_names.iter().filter(|(_,n)|pattern.matches(krate,n))
            .map(|(id,_)|*id).collect();
        assert_eq!(ids.len(),1,"source-qualified item lookup must be unique");ids[0]
    };
    let try_id=*resolve("core::ops::try_trait::Try").as_trait_decl().unwrap();
    let iterator=*resolve("core::iter::traits::iterator::Iterator").as_trait_decl().unwrap();
    let td=krate.trait_decls.get(try_id).unwrap();
    let outputs:Vec<_>=td.types.iter().filter(|(_,t)|t.skip_binder.name.0.as_str()=="Output").collect();
    assert_eq!(outputs.len(),1);
    let output=*outputs[0].0;
    assert!(outputs[0].1.params.is_empty(),"GAT Output unsupported");
    let fids:Vec<_>=krate.item_names.keys().filter_map(|id|id.as_fun().copied()).collect();
    let mut functions=HashMap::new();
    for id in fids {
        if let Some(f)=krate.fun_decls.get(id) {
            if let Some(p)=plan(&f.generics,Scope::Free,try_id,output) {functions.insert(id,p);}
        }
    }
    assert_eq!(functions.len(),3,"candidate is scoped to the audited R396 binder census");
    for (id,p) in &functions {
        let f=krate.fun_decls.get_mut(*id).unwrap();
        rewrite(&mut f.signature,p.slot,p.scope,&p.projection);
        rewrite(&mut f.body,p.slot,p.scope,&p.projection);
        rewrite(&mut f.src,p.slot,p.scope,&p.projection);
        rewrite_params(&mut f.generics,p);
    }
    let td=krate.trait_decls.get_mut(iterator).unwrap();
    let mids:Vec<_>=td.methods.iter().filter(|(_,m)|m.skip_binder.name.0.as_str()=="try_fold")
        .map(|(id,_)|*id).collect();
    assert_eq!(mids.len(),1);let method=mids[0];
    let b=td.methods.get_mut(&method).unwrap();
    let mp=plan(&b.params,Scope::Bound,try_id,output).unwrap();
    rewrite(&mut b.skip_binder.signature,mp.slot,mp.scope,&mp.projection);
    rewrite(&mut b.skip_binder.default,mp.slot,mp.scope,&mp.projection);
    rewrite_params(&mut b.params,&mp);
    let iids:Vec<_>=krate.item_names.keys().filter_map(|id|id.as_trait_impl().copied()).collect();
    let mut implementations=0;
    for id in iids {
        if let Some(i)=krate.trait_impls.get_mut(id) {
            if i.impl_trait.id==iterator {
                if let Some(b)=i.methods.get_mut(&method) {
                    let p=plan(&b.params,Scope::Bound,try_id,output).unwrap();
                    assert_eq!(p.slot,mp.slot);assert_eq!(p.old_types,mp.old_types);
                    rewrite(&mut b.skip_binder,p.slot,p.scope,&p.projection);
                    rewrite_params(&mut b.params,&p);
                    implementations+=1;
                }
            }
        }
    }
    assert_eq!(implementations,4,"candidate is scoped to the audited R396 method census");
    let mut vis=RewriteRefs {functions,iterator,method,method_plan:mp,direct_count:0,dispatch_count:0};
    let _=krate.drive_mut(&mut vis);
    assert_eq!(vis.direct_count,5,"unexpected function reference scope");
    assert_eq!(vis.dispatch_count,4,"unexpected trait dispatch scope");
    eprintln!("R419 candidate: 3 functions, 1 method, 4 impl binders, 5 direct refs, 4 dispatch refs. UNVERIFIED semantic boundary.");
    data.serialize_to_file(Path::new(&a[2]),SerializationFormat::Json).unwrap();
}
