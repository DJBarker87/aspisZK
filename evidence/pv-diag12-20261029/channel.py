module('JSONStdout','import PV_DIAG12_Line',[
'''/-! A streaming composition for ONE serialization followed by ONE newline.
`chunks` must still be associated to serde_json Value::fmt, including its
allocated error conversion. This is not a deployed DIAG_JSON_STDOUT instance.
No decoder, observer, NativeEvent or existing Link is redefined here. -/
def jsonStream (sig : Signal) (fuel : Nat) : List Span → Buffer → Cursor → BRun Unit
 | [],b,c => pureB () b c
 | s::ss,b,c => bindB (lineAll 1 sig fuel s b c) fun _ b c => jsonStream sig fuel ss b c
def onePrintln (sig : Signal) (fuel : Nat) (chunks : List Span) (newline : Span)
 (b : Buffer) (c : Cursor) : BRun Unit :=
 bindB (jsonStream sig fuel chunks b c) fun _ b c => lineAll 1 sig fuel newline b c
theorem jsonStream_nil (sig : Signal) (fuel : Nat) (b : Buffer) (c : Cursor) :
 jsonStream sig fuel [] b c=pureB () b c := rfl''',
'''theorem jsonStream_cons (sig : Signal) (fuel : Nat) (s : Span) (ss : List Span) (b : Buffer) (c : Cursor) :
 jsonStream sig fuel (s::ss) b c=
 bindB (lineAll 1 sig fuel s b c) (fun _ b c => jsonStream sig fuel ss b c) := rfl''',
'''theorem jsonStream_error_stops (sig : Signal) (fuel : Nat) (s : Span) (ss : List Span)
 (b after : Buffer) (c next : Cursor) (es : List Exchange) (e : Int)
 (h : lineAll 1 sig fuel s b c=⟨⟨es,.error e⟩,after,next⟩) :
 jsonStream sig fuel (s::ss) b c=⟨⟨es,.error e⟩,after,next⟩ := by
 simp only [jsonStream,h,bindB]''',
'''theorem jsonStream_cut_stops (sig : Signal) (fuel : Nat) (s : Span) (ss : List Span)
 (b after : Buffer) (c next : Cursor) (es : List Exchange)
 (h : lineAll 1 sig fuel s b c=⟨⟨es,.cut⟩,after,next⟩) :
 jsonStream sig fuel (s::ss) b c=⟨⟨es,.cut⟩,after,next⟩ := by
 simp only [jsonStream,h,bindB]''',
'''theorem println_error_no_newline (sig : Signal) (fuel : Nat) (ss : List Span) (newline : Span)
 (b after : Buffer) (c next : Cursor) (es : List Exchange) (e : Int)
 (h : jsonStream sig fuel ss b c=⟨⟨es,.error e⟩,after,next⟩) :
 onePrintln sig fuel ss newline b c=⟨⟨es,.error e⟩,after,next⟩ := by
 simp only [onePrintln,h,bindB]''',
'''theorem println_cut_no_newline (sig : Signal) (fuel : Nat) (ss : List Span) (newline : Span)
 (b after : Buffer) (c next : Cursor) (es : List Exchange)
 (h : jsonStream sig fuel ss b c=⟨⟨es,.cut⟩,after,next⟩) :
 onePrintln sig fuel ss newline b c=⟨⟨es,.cut⟩,after,next⟩ := by
 simp only [onePrintln,h,bindB]''',
'''theorem println_serialization_then_newline (sig : Signal) (fuel : Nat) (ss : List Span) (newline : Span)
 (b after : Buffer) (c next : Cursor) (es : List Exchange)
 (h : jsonStream sig fuel ss b c=⟨⟨es,.ok ()⟩,after,next⟩) :
 onePrintln sig fuel ss newline b c=
 let r := lineAll 1 sig fuel newline after next
 ⟨⟨es++r.execution.trace,r.execution.result⟩,r.buffer,r.cursor⟩ := by
 simp only [onePrintln,h,bindB]''',
'''theorem println_delivered_prefix (sig : Signal) (fuel : Nat) (ss : List Span) (newline : Span)
 (b after : Buffer) (c next : Cursor) (es : List Exchange)
 (h : jsonStream sig fuel ss b c=⟨⟨es,.ok ()⟩,after,next⟩) :
 delivered 1 (onePrintln sig fuel ss newline b c).execution.trace=
 delivered 1 es++delivered 1 (lineAll 1 sig fuel newline after next).execution.trace := by
 rw [println_serialization_then_newline sig fuel ss newline b after c next es h]
 exact delivered_append 1 es _''',
'''theorem println_requests_prefix (sig : Signal) (fuel : Nat) (ss : List Span) (newline : Span)
 (b after : Buffer) (c next : Cursor) (es : List Exchange)
 (h : jsonStream sig fuel ss b c=⟨⟨es,.ok ()⟩,after,next⟩) :
 requested (onePrintln sig fuel ss newline b c).execution.trace=
 requested es++requested (lineAll 1 sig fuel newline after next).execution.trace := by
 rw [println_serialization_then_newline sig fuel ss newline b after c next es h]
 exact requested_append es _''',
])
