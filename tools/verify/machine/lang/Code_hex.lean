import Machine
import Attr_hex
open X86

namespace Code_hex

def table : List (Nat × Instr × Nat) := [
  (0x50000, .movv false 0 (.m .rsi 0x0), 0x50004),
  (0x50004, .movv false 1 (.m .rsi 0x10), 0x50009),
  (0x50009, .movv false 5 (.c 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F#128), 0x50011),
  (0x50011, .movv false 6 (.c 0x09090909090909090909090909090909#128), 0x50019),
  (0x50019, .movv false 7 (.c 0x27272727272727272727272727272727#128), 0x50021),
  (0x50021, .movv false 8 (.c 0x30303030303030303030303030303030#128), 0x5002A),
  (0x5002A, .movv false 2 (.x 0), 0x5002E),
  (0x5002E, .psrlw 2 4, 0x50033),
  (0x50033, .pand 2 (.x 5), 0x50037),
  (0x50037, .pand 0 (.x 5), 0x5003B),
  (0x5003B, .movv false 3 (.x 2), 0x5003F),
  (0x5003F, .punpcklbw 3 (.x 0), 0x50043),
  (0x50043, .punpckhbw 2 (.x 0), 0x50047),
  (0x50047, .movv false 4 (.x 3), 0x5004B),
  (0x5004B, .pcmpgtb 4 (.x 6), 0x5004F),
  (0x5004F, .pand 4 (.x 7), 0x50053),
  (0x50053, .paddb 3 (.x 4), 0x50057),
  (0x50057, .paddb 3 (.x 8), 0x5005C),
  (0x5005C, .movv false 4 (.x 2), 0x50060),
  (0x50060, .pcmpgtb 4 (.x 6), 0x50064),
  (0x50064, .pand 4 (.x 7), 0x50068),
  (0x50068, .paddb 2 (.x 4), 0x5006C),
  (0x5006C, .paddb 2 (.x 8), 0x50071),
  (0x50071, .storev false .rdi 0x0 3, 0x50075),
  (0x50075, .storev false .rdi 0x10 2, 0x5007A),
  (0x5007A, .movv false 2 (.x 1), 0x5007E),
  (0x5007E, .psrlw 2 4, 0x50083),
  (0x50083, .pand 2 (.x 5), 0x50087),
  (0x50087, .pand 1 (.x 5), 0x5008B),
  (0x5008B, .movv false 3 (.x 2), 0x5008F),
  (0x5008F, .punpcklbw 3 (.x 1), 0x50093),
  (0x50093, .punpckhbw 2 (.x 1), 0x50097),
  (0x50097, .movv false 4 (.x 3), 0x5009B),
  (0x5009B, .pcmpgtb 4 (.x 6), 0x5009F),
  (0x5009F, .pand 4 (.x 7), 0x500A3),
  (0x500A3, .paddb 3 (.x 4), 0x500A7),
  (0x500A7, .paddb 3 (.x 8), 0x500AC),
  (0x500AC, .movv false 4 (.x 2), 0x500B0),
  (0x500B0, .pcmpgtb 4 (.x 6), 0x500B4),
  (0x500B4, .pand 4 (.x 7), 0x500B8),
  (0x500B8, .paddb 2 (.x 4), 0x500BC),
  (0x500BC, .paddb 2 (.x 8), 0x500C1),
  (0x500C1, .storev false .rdi 0x20 3, 0x500C6),
  (0x500C6, .storev false .rdi 0x30 2, 0x500CB),
  (0x500CB, .ret, 0x500CC)
]

def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

@[hex_at] theorem at_50000 : prog 0x50000 = some (.movv false 0 (.m .rsi 0x0), 0x50004) := rfl
@[hex_at] theorem at_50004 : prog 0x50004 = some (.movv false 1 (.m .rsi 0x10), 0x50009) := rfl
@[hex_at] theorem at_50009 : prog 0x50009 = some (.movv false 5 (.c 0x0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F0F#128), 0x50011) := rfl
@[hex_at] theorem at_50011 : prog 0x50011 = some (.movv false 6 (.c 0x09090909090909090909090909090909#128), 0x50019) := rfl
@[hex_at] theorem at_50019 : prog 0x50019 = some (.movv false 7 (.c 0x27272727272727272727272727272727#128), 0x50021) := rfl
@[hex_at] theorem at_50021 : prog 0x50021 = some (.movv false 8 (.c 0x30303030303030303030303030303030#128), 0x5002A) := rfl
@[hex_at] theorem at_5002A : prog 0x5002A = some (.movv false 2 (.x 0), 0x5002E) := rfl
@[hex_at] theorem at_5002E : prog 0x5002E = some (.psrlw 2 4, 0x50033) := rfl
@[hex_at] theorem at_50033 : prog 0x50033 = some (.pand 2 (.x 5), 0x50037) := rfl
@[hex_at] theorem at_50037 : prog 0x50037 = some (.pand 0 (.x 5), 0x5003B) := rfl
@[hex_at] theorem at_5003B : prog 0x5003B = some (.movv false 3 (.x 2), 0x5003F) := rfl
@[hex_at] theorem at_5003F : prog 0x5003F = some (.punpcklbw 3 (.x 0), 0x50043) := rfl
@[hex_at] theorem at_50043 : prog 0x50043 = some (.punpckhbw 2 (.x 0), 0x50047) := rfl
@[hex_at] theorem at_50047 : prog 0x50047 = some (.movv false 4 (.x 3), 0x5004B) := rfl
@[hex_at] theorem at_5004B : prog 0x5004B = some (.pcmpgtb 4 (.x 6), 0x5004F) := rfl
@[hex_at] theorem at_5004F : prog 0x5004F = some (.pand 4 (.x 7), 0x50053) := rfl
@[hex_at] theorem at_50053 : prog 0x50053 = some (.paddb 3 (.x 4), 0x50057) := rfl
@[hex_at] theorem at_50057 : prog 0x50057 = some (.paddb 3 (.x 8), 0x5005C) := rfl
@[hex_at] theorem at_5005C : prog 0x5005C = some (.movv false 4 (.x 2), 0x50060) := rfl
@[hex_at] theorem at_50060 : prog 0x50060 = some (.pcmpgtb 4 (.x 6), 0x50064) := rfl
@[hex_at] theorem at_50064 : prog 0x50064 = some (.pand 4 (.x 7), 0x50068) := rfl
@[hex_at] theorem at_50068 : prog 0x50068 = some (.paddb 2 (.x 4), 0x5006C) := rfl
@[hex_at] theorem at_5006C : prog 0x5006C = some (.paddb 2 (.x 8), 0x50071) := rfl
@[hex_at] theorem at_50071 : prog 0x50071 = some (.storev false .rdi 0x0 3, 0x50075) := rfl
@[hex_at] theorem at_50075 : prog 0x50075 = some (.storev false .rdi 0x10 2, 0x5007A) := rfl
@[hex_at] theorem at_5007A : prog 0x5007A = some (.movv false 2 (.x 1), 0x5007E) := rfl
@[hex_at] theorem at_5007E : prog 0x5007E = some (.psrlw 2 4, 0x50083) := rfl
@[hex_at] theorem at_50083 : prog 0x50083 = some (.pand 2 (.x 5), 0x50087) := rfl
@[hex_at] theorem at_50087 : prog 0x50087 = some (.pand 1 (.x 5), 0x5008B) := rfl
@[hex_at] theorem at_5008B : prog 0x5008B = some (.movv false 3 (.x 2), 0x5008F) := rfl
@[hex_at] theorem at_5008F : prog 0x5008F = some (.punpcklbw 3 (.x 1), 0x50093) := rfl
@[hex_at] theorem at_50093 : prog 0x50093 = some (.punpckhbw 2 (.x 1), 0x50097) := rfl
@[hex_at] theorem at_50097 : prog 0x50097 = some (.movv false 4 (.x 3), 0x5009B) := rfl
@[hex_at] theorem at_5009B : prog 0x5009B = some (.pcmpgtb 4 (.x 6), 0x5009F) := rfl
@[hex_at] theorem at_5009F : prog 0x5009F = some (.pand 4 (.x 7), 0x500A3) := rfl
@[hex_at] theorem at_500A3 : prog 0x500A3 = some (.paddb 3 (.x 4), 0x500A7) := rfl
@[hex_at] theorem at_500A7 : prog 0x500A7 = some (.paddb 3 (.x 8), 0x500AC) := rfl
@[hex_at] theorem at_500AC : prog 0x500AC = some (.movv false 4 (.x 2), 0x500B0) := rfl
@[hex_at] theorem at_500B0 : prog 0x500B0 = some (.pcmpgtb 4 (.x 6), 0x500B4) := rfl
@[hex_at] theorem at_500B4 : prog 0x500B4 = some (.pand 4 (.x 7), 0x500B8) := rfl
@[hex_at] theorem at_500B8 : prog 0x500B8 = some (.paddb 2 (.x 4), 0x500BC) := rfl
@[hex_at] theorem at_500BC : prog 0x500BC = some (.paddb 2 (.x 8), 0x500C1) := rfl
@[hex_at] theorem at_500C1 : prog 0x500C1 = some (.storev false .rdi 0x20 3, 0x500C6) := rfl
@[hex_at] theorem at_500C6 : prog 0x500C6 = some (.storev false .rdi 0x30 2, 0x500CB) := rfl
@[hex_at] theorem at_500CB : prog 0x500CB = some (.ret, 0x500CC) := rfl

end Code_hex
