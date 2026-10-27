// Safe generic move reference. No Copy or Clone bound, allocation or Drop.
pub fn pop_move_reference<T>(v: &mut Vec<T>) -> Option<T> {
    let n = v.len();
    if n == 0 { None } else { Some(v.remove(n - 1)) }
}

// Same reference with owned input/output, suitable for a functional adapter.
pub fn pop_move_owned<T>(mut v: Vec<T>) -> (Option<T>, Vec<T>) {
    let last = pop_move_reference(&mut v);
    (last, v)
}
