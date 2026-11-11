import X86

/-! # From bytes to instructions

The decoder for the instruction forms this model has: with it a program is its bytes, and what
llvm-objdump says they are is checked here, not relied on. Anything it does not know is `none`,
so a run through such a byte is a fault. (Intel SDM vol. 2: REX, ModRM, SIB, and each opcode's
entry.) -/

namespace X86

/-- A register by its number (the REX bit included): the ten this model has. -/
def regOf : Nat → Option Reg
  | 0 => some .rax | 1 => some .rcx | 2 => some .rdx | 3 => some .rbx | 4 => some .rsp | 5 => some .rbp
  | 6 => some .rsi | 7 => some .rdi | 8 => some .r8 | 14 => some .r14 | _ => none

/-- An 8-bit immediate or displacement, sign-extended. -/
def sext8 (b : Nat) : BitVec 64 := (BitVec.ofNat 8 b).signExtend 64

/-- Where a relative jump of `bits` bits goes from `next`. -/
def rel (next d bits : Nat) : Nat := if d < 2 ^ (bits - 1) then next + d else next + d - 2 ^ bits

def le32 (a b c d : Nat) : Nat := a + 256 * b + 65536 * c + 16777216 * d

/-- The r/m operand of a ModRM byte, and the bytes it took after that byte: a register; `[base]`;
`[base + disp8]`; `[base + index]` (SIB with scale 1 and no displacement). -/
def rmOperand (rexX rexB md rm : Nat) (rest : List Nat) : Option (Opnd × Nat) :=
  if md = 3 then (regOf (rm + 8 * rexB)).map fun r => (.reg r, 0)
  else if rm = 4 then
    match rest with
    | sib :: rest' =>
      let index := sib / 8 % 8 + 8 * rexX
      let base := sib % 8 + 8 * rexB
      if md = 0 ∧ sib / 64 = 0 ∧ sib % 8 ≠ 5 then
        if index = 4 then (regOf base).map fun b => (.mem b 0, 1)
        else (regOf base).bind fun b => (regOf index).map fun i => (.memi b i, 1)
      else if md = 1 ∧ index = 4 then
        match rest' with
        | d :: _ => (regOf base).map fun b => (.mem b (sext8 d), 2)
        | [] => none
      else none
    | [] => none
  else if md = 0 ∧ rm ≠ 5 then (regOf (rm + 8 * rexB)).map fun r => (.mem r 0, 0)
  else if md = 1 then
    match rest with
    | d :: _ => (regOf (rm + 8 * rexB)).map fun r => (.mem r (sext8 d), 1)
    | [] => none
  else none

/-- One instruction after its REX prefix (`rex` is its low four bits, 0 if there is none):
the instruction and the address of the next. `pos` is the address of the opcode byte. -/
def decodeOp (rex pos : Nat) : List Nat → Option (Instr × Nat)
  | 0xC3 :: _ => some (.ret, pos + 1)
  | 0x74 :: d :: _ => some (.jcc .e (rel (pos + 2) d 8), pos + 2)
  | 0x75 :: d :: _ => some (.jcc .ne (rel (pos + 2) d 8), pos + 2)
  | 0xE8 :: a :: b :: c :: d :: _ => some (.call (rel (pos + 5) (le32 a b c d) 32), pos + 5)
  | 0xE9 :: a :: b :: c :: d :: _ => some (.jmp (rel (pos + 5) (le32 a b c d) 32), pos + 5)
  | op :: rest =>
    let w := if rex / 8 % 2 = 1 then 64 else 32
    let rexR := rex / 4 % 2
    let rexX := rex / 2 % 2
    let rexB := rex % 2
    if 0x50 ≤ op ∧ op < 0x58 then (regOf (op - 0x50 + 8 * rexB)).map fun r => (.push r, pos + 1)
    else if 0x58 ≤ op ∧ op < 0x60 then (regOf (op - 0x58 + 8 * rexB)).map fun r => (.pop r, pos + 1)
    else
      match rest with
      | m :: rest' =>
        (rmOperand rexX rexB (m / 64) (m % 8) rest').bind fun (rm, k) =>
          let next := pos + 2 + k
          let digit := m / 8 % 8
          let reg := regOf (digit + 8 * rexR)
          match op with
          | 0x89 => reg.map fun r => (.mov w rm (.reg r), next)
          | 0x8B => reg.map fun r => (.mov w (.reg r) rm, next)
          | 0x85 => reg.map fun r => (.test w rm (.reg r), next)
          | 0x31 => reg.map fun r => (.xor w rm (.reg r), next)
          | 0x33 => reg.map fun r => (.xor w (.reg r) rm, next)
          | 0x39 => reg.map fun r => (.cmp w rm (.reg r), next)
          | 0x01 => reg.map fun r => (.add w rm (.reg r), next)
          | 0x83 =>
            match rest'.drop k with
            | i :: _ => if digit = 0 then some (.add w rm (.imm (sext8 i)), next + 1) else none
            | [] => none
          | 0xC1 =>
            match rest'.drop k with
            | i :: _ =>
              if digit = 4 then some (.shl w rm i, next + 1)
              else if digit = 0 ∧ w = 32 then
                match rm with
                | .reg r => some (.rol32 r i, next + 1)
                | _ => none
              else none
            | [] => none
          | _ => none
      | [] => none
  | [] => none

/-- The instruction whose first byte is at `pc`, where `bytes` are the bytes from there on. -/
def decode (pc : Nat) : List Nat → Option (Instr × Nat)
  | b :: rest => if 0x40 ≤ b ∧ b < 0x50 then decodeOp (b - 0x40) (pc + 1) rest else decodeOp 0 pc (b :: rest)
  | [] => none

end X86
