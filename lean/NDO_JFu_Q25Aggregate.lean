import NDO_JFu_Q25Block00
import NDO_JFu_Q25Window01
import NDO_JFu_Q25Window09
import NDO_JFu_Q25Window17
import NDO_JFu_Q25Window25
import NDO_JFu_Q25Window33
import NDO_JFu_Q25Window41
import NDO_JFu_Q25Window49
import NDO_JFu_Q25Window57
set_option autoImplicit false
namespace AspisR1.JFu_Q25Absorb
open JFp_SHA256
theorem lenB00 : B00.input.length=64 := by rfl
#print axioms lenB00
theorem lenB01 : B01.input.length=64 := by rfl
#print axioms lenB01
theorem lenB02 : B02.input.length=64 := by rfl
#print axioms lenB02
theorem lenB03 : B03.input.length=64 := by rfl
#print axioms lenB03
theorem lenB04 : B04.input.length=64 := by rfl
#print axioms lenB04
theorem lenB05 : B05.input.length=64 := by rfl
#print axioms lenB05
theorem lenB06 : B06.input.length=64 := by rfl
#print axioms lenB06
theorem lenB07 : B07.input.length=64 := by rfl
#print axioms lenB07
theorem lenB08 : B08.input.length=64 := by rfl
#print axioms lenB08
theorem lenB09 : B09.input.length=64 := by rfl
#print axioms lenB09
theorem lenB10 : B10.input.length=64 := by rfl
#print axioms lenB10
theorem lenB11 : B11.input.length=64 := by rfl
#print axioms lenB11
theorem lenB12 : B12.input.length=64 := by rfl
#print axioms lenB12
theorem lenB13 : B13.input.length=64 := by rfl
#print axioms lenB13
theorem lenB14 : B14.input.length=64 := by rfl
#print axioms lenB14
theorem lenB15 : B15.input.length=64 := by rfl
#print axioms lenB15
theorem lenB16 : B16.input.length=64 := by rfl
#print axioms lenB16
theorem lenB17 : B17.input.length=64 := by rfl
#print axioms lenB17
theorem lenB18 : B18.input.length=64 := by rfl
#print axioms lenB18
theorem lenB19 : B19.input.length=64 := by rfl
#print axioms lenB19
theorem lenB20 : B20.input.length=64 := by rfl
#print axioms lenB20
theorem lenB21 : B21.input.length=64 := by rfl
#print axioms lenB21
theorem lenB22 : B22.input.length=64 := by rfl
#print axioms lenB22
theorem lenB23 : B23.input.length=64 := by rfl
#print axioms lenB23
theorem lenB24 : B24.input.length=64 := by rfl
#print axioms lenB24
theorem lenB25 : B25.input.length=64 := by rfl
#print axioms lenB25
theorem lenB26 : B26.input.length=64 := by rfl
#print axioms lenB26
theorem lenB27 : B27.input.length=64 := by rfl
#print axioms lenB27
theorem lenB28 : B28.input.length=64 := by rfl
#print axioms lenB28
theorem lenB29 : B29.input.length=64 := by rfl
#print axioms lenB29
theorem lenB30 : B30.input.length=64 := by rfl
#print axioms lenB30
theorem lenB31 : B31.input.length=64 := by rfl
#print axioms lenB31
theorem lenB32 : B32.input.length=64 := by rfl
#print axioms lenB32
theorem lenB33 : B33.input.length=64 := by rfl
#print axioms lenB33
theorem lenB34 : B34.input.length=64 := by rfl
#print axioms lenB34
theorem lenB35 : B35.input.length=64 := by rfl
#print axioms lenB35
theorem lenB36 : B36.input.length=64 := by rfl
#print axioms lenB36
theorem lenB37 : B37.input.length=64 := by rfl
#print axioms lenB37
theorem lenB38 : B38.input.length=64 := by rfl
#print axioms lenB38
theorem lenB39 : B39.input.length=64 := by rfl
#print axioms lenB39
theorem lenB40 : B40.input.length=64 := by rfl
#print axioms lenB40
theorem lenB41 : B41.input.length=64 := by rfl
#print axioms lenB41
theorem lenB42 : B42.input.length=64 := by rfl
#print axioms lenB42
theorem lenB43 : B43.input.length=64 := by rfl
#print axioms lenB43
theorem lenB44 : B44.input.length=64 := by rfl
#print axioms lenB44
theorem lenB45 : B45.input.length=64 := by rfl
#print axioms lenB45
theorem lenB46 : B46.input.length=64 := by rfl
#print axioms lenB46
theorem lenB47 : B47.input.length=64 := by rfl
#print axioms lenB47
theorem lenB48 : B48.input.length=64 := by rfl
#print axioms lenB48
theorem lenB49 : B49.input.length=64 := by rfl
#print axioms lenB49
theorem lenB50 : B50.input.length=64 := by rfl
#print axioms lenB50
theorem lenB51 : B51.input.length=64 := by rfl
#print axioms lenB51
theorem lenB52 : B52.input.length=64 := by rfl
#print axioms lenB52
theorem lenB53 : B53.input.length=64 := by rfl
#print axioms lenB53
theorem lenB54 : B54.input.length=64 := by rfl
#print axioms lenB54
theorem lenB55 : B55.input.length=64 := by rfl
#print axioms lenB55
theorem lenB56 : B56.input.length=64 := by rfl
#print axioms lenB56
theorem lenB57 : B57.input.length=64 := by rfl
#print axioms lenB57
theorem lenB58 : B58.input.length=64 := by rfl
#print axioms lenB58
def head : List (List Nat) := [B00.input,B01.input,B02.input,B03.input,B04.input,B05.input,B06.input,B07.input,B08.input,B09.input,B10.input,B11.input,B12.input,B13.input,B14.input,B15.input,B16.input,B17.input,B18.input,B19.input,B20.input,B21.input,B22.input,B23.input,B24.input,B25.input,B26.input,B27.input,B28.input,B29.input,B30.input,B31.input,B32.input,B33.input,B34.input,B35.input,B36.input,B37.input,B38.input,B39.input,B40.input,B41.input,B42.input,B43.input,B44.input,B45.input,B46.input,B47.input,B48.input,B49.input,B50.input,B51.input,B52.input,B53.input,B54.input,B55.input,B56.input,B57.input]
def tail : List Nat := [0,0,0,0,0,0,0,184,45,199,1,173,22,151,29,36,107,149,33,36,89,236,96,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def message : List Nat := head.flatten ++ tail
def chunks : List (List Nat) := head ++ [B58.input]
theorem tailLength : tail.length=39 := by rfl
#print axioms tailLength
theorem headLength : head.flatten.length=3712 := by
  simp only [head,List.length_flatten,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,lenB00,lenB01,lenB02,lenB03,lenB04,lenB05,lenB06,lenB07,lenB08,lenB09,lenB10,lenB11,lenB12,lenB13,lenB14,lenB15,lenB16,lenB17,lenB18,lenB19,lenB20,lenB21,lenB22,lenB23,lenB24,lenB25,lenB26,lenB27,lenB28,lenB29,lenB30,lenB31,lenB32,lenB33,lenB34,lenB35,lenB36,lenB37,lenB38,lenB39,lenB40,lenB41,lenB42,lenB43,lenB44,lenB45,lenB46,lenB47,lenB48,lenB49,lenB50,lenB51,lenB52,lenB53,lenB54,lenB55,lenB56,lenB57]
  omega
#print axioms headLength
theorem messageLength : message.length=3751 := by
  simp only [message,List.length_append,headLength,tailLength]
#print axioms messageLength
theorem tailPad : tail ++ [128] ++ List.replicate 16 0 ++ [0,0,0,0,0,0,117,56] = [B58.input].flatten := by rfl
#print axioms tailPad
theorem padded : pad message=chunks.flatten := by
  rw [pad,messageLength]
  change (head.flatten ++ tail) ++ [128] ++ List.replicate 16 0 ++ [0,0,0,0,0,0,117,56]=_
  simp only [List.append_assoc,chunks,List.flatten_append]
  exact congrArg (fun t => head.flatten ++ t) (by simpa only [List.append_assoc] using tailPad)
#print axioms padded
theorem lengths : ∀ c ∈ chunks,c.length=64 := by
  intro c hc
  simp only [chunks,head,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc] at hc
  rcases hc with h0|h1|h2|h3|h4|h5|h6|h7|h8|h9|h10|h11|h12|h13|h14|h15|h16|h17|h18|h19|h20|h21|h22|h23|h24|h25|h26|h27|h28|h29|h30|h31|h32|h33|h34|h35|h36|h37|h38|h39|h40|h41|h42|h43|h44|h45|h46|h47|h48|h49|h50|h51|h52|h53|h54|h55|h56|h57|h58
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
  · subst c; rfl
#print axioms lengths
theorem paddedLength : (pad message).length=3776 := by
  rw [padded]
  simp only [chunks,head,List.flatten_append,List.flatten_cons,List.flatten_nil,List.length_append,List.length_nil,List.length_flatten,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,lenB00,lenB01,lenB02,lenB03,lenB04,lenB05,lenB06,lenB07,lenB08,lenB09,lenB10,lenB11,lenB12,lenB13,lenB14,lenB15,lenB16,lenB17,lenB18,lenB19,lenB20,lenB21,lenB22,lenB23,lenB24,lenB25,lenB26,lenB27,lenB28,lenB29,lenB30,lenB31,lenB32,lenB33,lenB34,lenB35,lenB36,lenB37,lenB38,lenB39,lenB40,lenB41,lenB42,lenB43,lenB44,lenB45,lenB46,lenB47,lenB48,lenB49,lenB50,lenB51,lenB52,lenB53,lenB54,lenB55,lenB56,lenB57,lenB58]
#print axioms paddedLength
theorem blockList : blocks ((pad message).length/64) (pad message)=chunks := by
  rw [paddedLength,padded]
  exact blocks_chunks chunks lengths
#print axioms blockList
def result : Reg := B58.result
theorem checked : JFp_SHA256.hash message=result := by
  unfold JFp_SHA256.hash
  dsimp only
  rw [blockList]
  simp only [chunks,head,List.foldl_append,List.foldl_cons,List.foldl_nil]
  rw [show initial=B00.start from rfl,B00.checked]
  rw [show B00.result=B01.start from rfl,B01.checked]
  rw [show B01.result=B02.start from rfl,B02.checked]
  rw [show B02.result=B03.start from rfl,B03.checked]
  rw [show B03.result=B04.start from rfl,B04.checked]
  rw [show B04.result=B05.start from rfl,B05.checked]
  rw [show B05.result=B06.start from rfl,B06.checked]
  rw [show B06.result=B07.start from rfl,B07.checked]
  rw [show B07.result=B08.start from rfl,B08.checked]
  rw [show B08.result=B09.start from rfl,B09.checked]
  rw [show B09.result=B10.start from rfl,B10.checked]
  rw [show B10.result=B11.start from rfl,B11.checked]
  rw [show B11.result=B12.start from rfl,B12.checked]
  rw [show B12.result=B13.start from rfl,B13.checked]
  rw [show B13.result=B14.start from rfl,B14.checked]
  rw [show B14.result=B15.start from rfl,B15.checked]
  rw [show B15.result=B16.start from rfl,B16.checked]
  rw [show B16.result=B17.start from rfl,B17.checked]
  rw [show B17.result=B18.start from rfl,B18.checked]
  rw [show B18.result=B19.start from rfl,B19.checked]
  rw [show B19.result=B20.start from rfl,B20.checked]
  rw [show B20.result=B21.start from rfl,B21.checked]
  rw [show B21.result=B22.start from rfl,B22.checked]
  rw [show B22.result=B23.start from rfl,B23.checked]
  rw [show B23.result=B24.start from rfl,B24.checked]
  rw [show B24.result=B25.start from rfl,B25.checked]
  rw [show B25.result=B26.start from rfl,B26.checked]
  rw [show B26.result=B27.start from rfl,B27.checked]
  rw [show B27.result=B28.start from rfl,B28.checked]
  rw [show B28.result=B29.start from rfl,B29.checked]
  rw [show B29.result=B30.start from rfl,B30.checked]
  rw [show B30.result=B31.start from rfl,B31.checked]
  rw [show B31.result=B32.start from rfl,B32.checked]
  rw [show B32.result=B33.start from rfl,B33.checked]
  rw [show B33.result=B34.start from rfl,B34.checked]
  rw [show B34.result=B35.start from rfl,B35.checked]
  rw [show B35.result=B36.start from rfl,B36.checked]
  rw [show B36.result=B37.start from rfl,B37.checked]
  rw [show B37.result=B38.start from rfl,B38.checked]
  rw [show B38.result=B39.start from rfl,B39.checked]
  rw [show B39.result=B40.start from rfl,B40.checked]
  rw [show B40.result=B41.start from rfl,B41.checked]
  rw [show B41.result=B42.start from rfl,B42.checked]
  rw [show B42.result=B43.start from rfl,B43.checked]
  rw [show B43.result=B44.start from rfl,B44.checked]
  rw [show B44.result=B45.start from rfl,B45.checked]
  rw [show B45.result=B46.start from rfl,B46.checked]
  rw [show B46.result=B47.start from rfl,B47.checked]
  rw [show B47.result=B48.start from rfl,B48.checked]
  rw [show B48.result=B49.start from rfl,B49.checked]
  rw [show B49.result=B50.start from rfl,B50.checked]
  rw [show B50.result=B51.start from rfl,B51.checked]
  rw [show B51.result=B52.start from rfl,B52.checked]
  rw [show B52.result=B53.start from rfl,B53.checked]
  rw [show B53.result=B54.start from rfl,B54.checked]
  rw [show B54.result=B55.start from rfl,B55.checked]
  rw [show B55.result=B56.start from rfl,B56.checked]
  rw [show B56.result=B57.start from rfl,B57.checked]
  rw [show B57.result=B58.start from rfl,B58.checked]
  rfl
#print axioms checked
end AspisR1.JFu_Q25Absorb
