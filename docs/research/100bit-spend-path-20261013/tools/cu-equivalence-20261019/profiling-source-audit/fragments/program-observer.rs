fn observer()->verifier::Observer {
    #[cfg(feature="cu-profiling")] {Some(mark)}
    #[cfg(not(feature="cu-profiling"))] {None}
}