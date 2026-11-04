#[path="src/tools/r1-cost-probe/src/bin/user_client/diagnostics.rs"] mod diagnostics;
unsafe extern "C" { fn prctl(option:i32,...) -> i32; fn getrlimit(resource:u32,limit:*mut [u64;2])->i32; }
fn main(){diagnostics::initialize();let mut core=[1u64;2];assert_eq!(unsafe{getrlimit(4,&mut core)},0);println!("dumpable={} core={},{}",unsafe{prctl(3)},core[0],core[1]);print!("{}",std::fs::read_to_string("/proc/self/status").unwrap());panic!("forced private panic payload");}
