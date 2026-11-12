import Arm64
open Arm64

/-! The NEON `hex` kernel's 32 instruction words (from the ELF object), run on Google's AArch64 model
(`Arm64.Trusted`: its decoder and `execInst`), on concrete hashes, against the hexadecimal. -/

def hexWords : List (BitVec 32) := [
  0xad400420, 0x4f00e5e4, 0x4f00e525, 0x4f01e4e6, 0x4f01e607, 0x6f0c0402, 0x4e241c00, 0x6f0c0423,
  0x4e241c21, 0x4e003850, 0x4e007851, 0x4e013872, 0x4e017873, 0x6e253600, 0x6e253621, 0x6e253642,
  0x6e253663, 0x4e261c00, 0x4e261c21, 0x4e261c42, 0x4e261c63, 0x4e278610, 0x4e278631, 0x4e278652,
  0x4e278673, 0x4e208610, 0x4e218631, 0x4e228652, 0x4e238673, 0xad004410, 0xad014c12, 0xd65f03c0]

def hexText (bs : List (BitVec 8)) : List (BitVec 8) :=
  bs.flatMap fun (b : BitVec 8) => [b >>> 4, b &&& 15#8].map fun (n : BitVec 8) => if n < 10#8 then n + 0x30#8 else n + 0x57#8

def outAt : BitVec 64 := 0x7000#64
def inAt : BitVec 64 := 0x5000#64

/-- The state before the call: the hash readable at `inAt`, 64 writable bytes at `outAt`, the return
address in X30. Nothing else is mapped. -/
def start (hash : List (BitVec 8)) : State :=
  let mem : Memory := Memory.ofFn
    (fun a => if (a - inAt).toNat < 32 then hash.getD (a - inAt).toNat 0#8 else 0xEE#8)
    (fun a => if (a - inAt).toNat < 32 then some Perm.ro else if (a - outAt).toNat < 64 then some Perm.rw else none)
  ((({ mem := mem, pc := 0x10000#64 } : State).writeReg64 (.gpr 0#5) outAt).writeReg64 (.gpr 1#5) inAt).writeReg64 (.gpr 30#5) 0x424242#64

def run (hash : List (BitVec 8)) : State :=
  hexWords.foldl (fun s w => match decode w with | some i => execInst i s | none => { s with status := .Halted }) (start hash)

def ok (hash : List (BitVec 8)) : Bool :=
  let s := run hash
  s.pc == 0x424242#64 && s.status == .Running && s.mem.readBytes outAt 64 == hexText hash

def hashes : List (List (BitVec 8)) :=
  (List.range 256).map (fun v => List.replicate 32 (BitVec.ofNat 8 v)) ++
  (List.range 64).map (fun k => (List.range 32).map fun i => BitVec.ofNat 8 ((k * 2654435761 + i * 40503 + (k + 1) * i * i * 97) / 7))

#eval (hashes.length, (hashes.filter ok).length)
#eval let s := run ((List.range 32).map fun i => BitVec.ofNat 8 (i * 17 + 3)); (s.pc, s.status == .Running, String.ofList ((s.mem.readBytes outAt 64).map fun b => Char.ofNat b.toNat))
