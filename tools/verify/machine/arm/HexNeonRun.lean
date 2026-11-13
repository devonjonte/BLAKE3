import Arm64
import HexText
import Quiet_hex_neon
open Arm64

/-! The NEON `hex` kernel's instruction words (from the ELF object), run on Google's AArch64 model
(`Arm64.Trusted`: its decoder and `execInst`), on concrete hashes, against the hexadecimal. -/

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
  hex_neon_words.foldl (fun s w => match decode w with | some i => execInst i s | none => { s with status := .Halted }) (start hash)

def ok (hash : List (BitVec 8)) : Bool :=
  let s := run hash
  s.pc == 0x424242#64 && s.status == .Running && s.mem.readBytes outAt 64 == Hex.text hash

def hashes : List (List (BitVec 8)) :=
  (List.range 256).map (fun v => List.replicate 32 (BitVec.ofNat 8 v)) ++
  (List.range 64).map (fun k => (List.range 32).map fun i => BitVec.ofNat 8 ((k * 2654435761 + i * 40503 + (k + 1) * i * i * 97) / 7))

#eval (hashes.length, (hashes.filter ok).length)
#eval let s := run ((List.range 32).map fun i => BitVec.ofNat 8 (i * 17 + 3)); (s.pc, s.status == .Running, String.ofList ((s.mem.readBytes outAt 64).map fun b => Char.ofNat b.toNat))

/-- What the observer of `Observer.lean` sees on two different hashes: as many things each (every
instruction's fetch, a read, two writes, the return), and the same. -/
def seenOn (v : Nat) : Option (List Obs) := runObs hex_neon_words (start (List.replicate 32 (BitVec.ofNat 8 v)))

#eval ((seenOn 0x00).map (·.length), decide (seenOn 0x00 = seenOn 0xff))
