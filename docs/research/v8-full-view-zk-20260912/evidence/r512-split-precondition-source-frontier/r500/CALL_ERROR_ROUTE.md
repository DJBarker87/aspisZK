# Fun32 compact call/error route

The selected structured Fun32 first compares its two `Usize` inputs at the
LLBC conditional rooted at body statement 6. The failing branch constructs a
`core::fmt::Arguments` value using the two `NonNull` instantiations, then calls
foreign Fun33 `core::panicking::panic_nounwind_fmt`; its unwind and following
path terminate with `Abort UndefinedBehavior`.

This is a direct declaration/call census from the selected LLBC. The foreign
panic body is not present. No condition adequacy, native safety, or behavior
claim is made here.
