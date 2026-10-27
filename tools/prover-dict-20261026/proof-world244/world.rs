//! OS results are input values, never a replacement for a syscall. Each result,
//! including errors, consumes a position. Mismatch/exhaustion is explicit.
#[derive(Clone, Copy)]
pub struct Reply { pub operation: u8, pub value: i32, pub error: i32 }
#[derive(Clone, Copy)]
pub struct Tape { pub replies: [Reply; 16], pub used: usize }
pub struct Outcome { pub tape: Tape, pub reply: Option<Reply> }

pub fn next(mut tape: Tape, operation: u8) -> Outcome {
    if tape.used >= 16 { return Outcome { tape, reply: None }; }
    let reply = tape.replies[tape.used];
    if reply.operation != operation { return Outcome { tape, reply: None }; }
    tape.used += 1;
    Outcome { tape, reply: Some(reply) }
}

/// Kind-only reserve branch after native code has received the OS result.
pub fn retry_collision(errno: i32) -> bool { errno == 17 }

