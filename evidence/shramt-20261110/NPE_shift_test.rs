// NPE_ 2026-11-10: Rust shift semantics for the ShrAmt bridge check.
// Built twice: -C overflow-checks=on and -C overflow-checks=off (both -O and plain).
use std::hint::black_box;
use std::panic;

fn run<F: FnOnce() -> String + panic::UnwindSafe>(label: &str, f: F) {
    match panic::catch_unwind(f) {
        Ok(s) => println!("{label}: ok {s}"),
        Err(e) => {
            let msg = e.downcast_ref::<String>().cloned()
                .or_else(|| e.downcast_ref::<&str>().map(|s| s.to_string()))
                .unwrap_or_default();
            println!("{label}: PANIC {msg}");
        }
    }
}

// ShrAmt model, OFF configuration: amount `as u32`, then the library wrapping shift masks by numBits (64 here).
fn model_wrap_shr(x: usize, a: u32) -> usize { x.wrapping_shr(a) }
fn model_wrap_shl(x: usize, a: u32) -> usize { x.wrapping_shl(a) }

fn main() {
    panic::set_hook(Box::new(|_| {}));
    println!("overflow_checks_cfg={}", cfg!(debug_assertions) as u8);
    println!("usize_bits={}", usize::BITS);
    let x: usize = black_box(0xdead_beef_1234_5678usize);
    println!("x={x:#x}");
    macro_rules! case_i32 { ($y:expr) => {{
        let y: i32 = black_box($y);
        run(&format!("shr usize by {}i32", $y), move || format!("{:#x}", x >> y));
        run(&format!("shl usize by {}i32", $y), move || format!("{:#x}", x << y));
        println!("  model(as u32={}) shr={:#x} shl={:#x}", y as u32, model_wrap_shr(x, y as u32), model_wrap_shl(x, y as u32));
    }}}
    macro_rules! case_usize { ($y:expr) => {{
        let y: usize = black_box($y);
        run(&format!("shr usize by {}usize", $y), move || format!("{:#x}", x >> y));
        run(&format!("shl usize by {}usize", $y), move || format!("{:#x}", x << y));
        println!("  model(as u32={}) shr={:#x} shl={:#x}", y as u32, model_wrap_shr(x, y as u32), model_wrap_shl(x, y as u32));
    }}}
    case_i32!(9i32);
    case_i32!(-1i32);
    case_i32!(40i32);
    case_i32!(64i32);
    case_i32!(65i32);
    case_i32!(-55i32);
    case_i32!(i32::MIN);
    case_usize!(9usize);
    case_usize!(40usize);
    case_usize!(64usize);
    case_usize!((1usize << 32) + 3);
    case_usize!(usize::MAX);
    // u32 left operand (bits 32) by i32 40: mask to 5 bits
    let w: u32 = black_box(0xdead_beefu32);
    let y: i32 = black_box(40i32);
    run("shr u32 by 40i32", move || format!("{:#x}", w >> y));
    println!("  model u32 (as u32=40) shr={:#x}", w.wrapping_shr(40));
}
