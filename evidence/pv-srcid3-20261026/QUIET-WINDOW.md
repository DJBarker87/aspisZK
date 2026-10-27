# Quiet-window exception receipt

The user fixed 17:45–18:15 UTC as a launch hold, regardless of shared marker
state. At 17:50 UTC preflight 25300 refused with quiet-window JSON; zero attempts.
At 17:54 UTC retry 25301 unexpectedly passed reservation and the existing task
client immediately launched the shared launcher. The CheckedEncoding compile
exited 0 in 1.83s, peak RSS 4109048 KiB, zero swaps, standard axioms. This is
a process violation of the fixed user hold, despite the shared preflight allowing
it. It is charged as one Lean attempt; it is not disguised as a refusal.

The scope had ended before discovery. No marker was edited or deleted.
The task client now checks the user's absolute hold locally before any host
reservation or launch. No more capped scopes will start before 18:15 UTC.
The raw successful reservation, launcher, output and time receipts are retained.
