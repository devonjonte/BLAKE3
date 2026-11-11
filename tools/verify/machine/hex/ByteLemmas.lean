import X86
open X86

/-! Bytes of the values the model reads: what a 32-, 64- or 128-bit load followed by a store moves is the bytes. Written by a script. -/

theorem byte32_0 (b0 b1 b2 b3 : BitVec 8) : byte (((BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24) &&& 4294967295#64) &&& 4294967295#64) 0 = b0 := by
  simp only [byte]; bv_decide
theorem byte32_1 (b0 b1 b2 b3 : BitVec 8) : byte (((BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24) &&& 4294967295#64) &&& 4294967295#64) 1 = b1 := by
  simp only [byte]; bv_decide
theorem byte32_2 (b0 b1 b2 b3 : BitVec 8) : byte (((BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24) &&& 4294967295#64) &&& 4294967295#64) 2 = b2 := by
  simp only [byte]; bv_decide
theorem byte32_3 (b0 b1 b2 b3 : BitVec 8) : byte (((BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24) &&& 4294967295#64) &&& 4294967295#64) 3 = b3 := by
  simp only [byte]; bv_decide
theorem byte64_0 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : byte (BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24 ||| BitVec.setWidth 64 b4 <<< 32 ||| BitVec.setWidth 64 b5 <<< 40 ||| BitVec.setWidth 64 b6 <<< 48 ||| BitVec.setWidth 64 b7 <<< 56) 0 = b0 := by
  simp only [byte]; bv_decide
theorem byte64_1 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : byte (BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24 ||| BitVec.setWidth 64 b4 <<< 32 ||| BitVec.setWidth 64 b5 <<< 40 ||| BitVec.setWidth 64 b6 <<< 48 ||| BitVec.setWidth 64 b7 <<< 56) 1 = b1 := by
  simp only [byte]; bv_decide
theorem byte64_2 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : byte (BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24 ||| BitVec.setWidth 64 b4 <<< 32 ||| BitVec.setWidth 64 b5 <<< 40 ||| BitVec.setWidth 64 b6 <<< 48 ||| BitVec.setWidth 64 b7 <<< 56) 2 = b2 := by
  simp only [byte]; bv_decide
theorem byte64_3 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : byte (BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24 ||| BitVec.setWidth 64 b4 <<< 32 ||| BitVec.setWidth 64 b5 <<< 40 ||| BitVec.setWidth 64 b6 <<< 48 ||| BitVec.setWidth 64 b7 <<< 56) 3 = b3 := by
  simp only [byte]; bv_decide
theorem byte64_4 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : byte (BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24 ||| BitVec.setWidth 64 b4 <<< 32 ||| BitVec.setWidth 64 b5 <<< 40 ||| BitVec.setWidth 64 b6 <<< 48 ||| BitVec.setWidth 64 b7 <<< 56) 4 = b4 := by
  simp only [byte]; bv_decide
theorem byte64_5 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : byte (BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24 ||| BitVec.setWidth 64 b4 <<< 32 ||| BitVec.setWidth 64 b5 <<< 40 ||| BitVec.setWidth 64 b6 <<< 48 ||| BitVec.setWidth 64 b7 <<< 56) 5 = b5 := by
  simp only [byte]; bv_decide
theorem byte64_6 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : byte (BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24 ||| BitVec.setWidth 64 b4 <<< 32 ||| BitVec.setWidth 64 b5 <<< 40 ||| BitVec.setWidth 64 b6 <<< 48 ||| BitVec.setWidth 64 b7 <<< 56) 6 = b6 := by
  simp only [byte]; bv_decide
theorem byte64_7 (b0 b1 b2 b3 b4 b5 b6 b7 : BitVec 8) : byte (BitVec.setWidth 64 b0 ||| BitVec.setWidth 64 b1 <<< 8 ||| BitVec.setWidth 64 b2 <<< 16 ||| BitVec.setWidth 64 b3 <<< 24 ||| BitVec.setWidth 64 b4 <<< 32 ||| BitVec.setWidth 64 b5 <<< 40 ||| BitVec.setWidth 64 b6 <<< 48 ||| BitVec.setWidth 64 b7 <<< 56) 7 = b7 := by
  simp only [byte]; bv_decide
theorem by8_0 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 0 = b0 := by
  simp only [by8]; bv_decide
theorem by8_1 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 1 = b1 := by
  simp only [by8]; bv_decide
theorem by8_2 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 2 = b2 := by
  simp only [by8]; bv_decide
theorem by8_3 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 3 = b3 := by
  simp only [by8]; bv_decide
theorem by8_4 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 4 = b4 := by
  simp only [by8]; bv_decide
theorem by8_5 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 5 = b5 := by
  simp only [by8]; bv_decide
theorem by8_6 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 6 = b6 := by
  simp only [by8]; bv_decide
theorem by8_7 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 7 = b7 := by
  simp only [by8]; bv_decide
theorem by8_8 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 8 = b8 := by
  simp only [by8]; bv_decide
theorem by8_9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 9 = b9 := by
  simp only [by8]; bv_decide
theorem by8_10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 10 = b10 := by
  simp only [by8]; bv_decide
theorem by8_11 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 11 = b11 := by
  simp only [by8]; bv_decide
theorem by8_12 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 12 = b12 := by
  simp only [by8]; bv_decide
theorem by8_13 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 13 = b13 := by
  simp only [by8]; bv_decide
theorem by8_14 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 14 = b14 := by
  simp only [by8]; bv_decide
theorem by8_15 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : BitVec 8) : by8 (b15 ++ b14 ++ b13 ++ b12 ++ b11 ++ b10 ++ b9 ++ b8 ++ b7 ++ b6 ++ b5 ++ b4 ++ b3 ++ b2 ++ b1 ++ b0) 15 = b15 := by
  simp only [by8]; bv_decide

macro "bytes_simp" : term => `(True)
