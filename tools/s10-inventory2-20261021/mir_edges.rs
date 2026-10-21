#![feature(rustc_private)]
extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_hir;

use rustc_driver::{Callbacks, Compilation};
use rustc_interface::interface;
use rustc_middle::{mir::TerminatorKind, ty::{self, TyCtxt}};
use std::{env, fs::File, io::Write};

struct Probe;
impl Callbacks for Probe {
    fn after_analysis<'tcx>(&mut self, _: &interface::Compiler, tcx: TyCtxt<'tcx>) -> Compilation {
        let module = env::var("S10_MODULE").unwrap();
        let mut out = File::create(env::var("S10_OUTPUT").unwrap()).unwrap();
        for local in tcx.mir_keys(()) {
            let def = local.to_def_id();
            let path = tcx.def_path_str(def);
            let parts: Vec<_> = path.split("::").collect();
            if module != "*" && parts.get(1).copied() != Some(module.as_str()) { continue; }
            let span = tcx.sess.source_map().span_to_diagnostic_string(tcx.def_span(def));
            writeln!(out, "D\t{:?}\t{:?}\t{:?}", path, span, tcx.generics_of(def)).unwrap();
            let body = tcx.optimized_mir(def);
            for (bb, block) in body.basic_blocks.iter_enumerated() {
                let term = block.terminator();
                let site = tcx.sess.source_map().span_to_diagnostic_string(term.source_info.span);
                match &term.kind {
                    TerminatorKind::Call { func, args, .. } => {
                        let ty = func.ty(&body.local_decls, tcx);
                        match ty.kind() {
                            ty::FnDef(target, generics) => writeln!(out,
                                "C\t{:?}\t{:?}\t{:?}\t{:?}\t{:?}\t{:?}",
                                path, bb, tcx.def_path_str(*target), format!("{generics:?}"), site,
                                format!("{args:?}")).unwrap(),
                            _ => writeln!(out, "I\t{:?}\t{:?}\t{:?}\t{:?}", path, bb, format!("{func:?}: {ty:?}"), site).unwrap(),
                        }
                    }
                    TerminatorKind::Drop { place, .. } => writeln!(out,
                        "X\t{:?}\t{:?}\t{:?}\t{:?}", path, bb,
                        format!("{:?}", place.ty(&body.local_decls, tcx).ty), site).unwrap(),
                    _ => {}
                }
            }
            // Keep MIR for independent inspection of indirect-register provenance.
            writeln!(out, "B\t{:?}\t{:?}", path, format!("{body:#?}")).unwrap();
        }
        Compilation::Stop
    }
}
fn main() {
    let mut args: Vec<String> = env::args().collect();
    // RUSTC_WORKSPACE_WRAPPER supplies the real rustc path as argv[1].
    if args.get(1).is_some_and(|s| s.ends_with("rustc")) { args.remove(1); }
    rustc_driver::run_compiler(&args, &mut Probe);
}
