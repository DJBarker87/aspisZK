//! Include the candidate's complete source module and append access adapters.
//! No kernel body is copied, rewritten, visibility-edited, or stubbed.
use proc_macro::{TokenStream, TokenTree};
#[proc_macro]
pub fn source_module(input: TokenStream) -> TokenStream {
    let mut it = input.into_iter();
    let name = it.next().unwrap().to_string();
    assert_eq!(it.next().unwrap().to_string(), ",");
    let path = it.next().unwrap().to_string();
    assert_eq!(it.next().unwrap().to_string(), ",");
    let TokenTree::Group(adapters) = it.next().unwrap() else { panic!("adapter block") };
    assert!(it.next().is_none());
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../..");
    let absolute = root.join(path.trim_matches('"')).canonicalize().unwrap();
    let source = std::fs::read_to_string(&absolute).unwrap();
    // Inner module documentation is not executable Rust. Keep all code verbatim.
    let source = source.lines().map(|s| if s.starts_with("//!") { "" } else { s })
        .collect::<Vec<_>>().join("\n");
    format!("const _: &str = include_str!({:?}); #[allow(dead_code, unexpected_cfgs)] pub(crate) mod {name} {{ {source}\n{} }}", absolute.to_str().unwrap(), adapters.stream())
        .parse().unwrap()
}
