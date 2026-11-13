import Lemmas_adler32
open X86

/-! Word operations available in Ode, for reductions around a raw-sums kernel.
These are arithmetic lemmas, independent of the optimized kernel's machine proof. -/
namespace Adler32

def fold16Nat (x : Nat) : Nat := x % 65536 + 15 * (x / 65536)

def fold16Word (x : BitVec 64) : BitVec 64 :=
  (x &&& 65535#64) + (((x >>> 16) <<< 4) - (x >>> 16))

theorem fold16Nat_mod (x : Nat) : fold16Nat x % 65521 = x % 65521 := by
  have hd := Nat.mod_add_div x 65536
  have he : x = 65521 * (x / 65536) + fold16Nat x := by unfold fold16Nat; omega
  have hm := congrArg (fun n : Nat => n % 65521) he
  simpa [Nat.add_mod, Nat.mul_mod] using hm.symm

theorem fold16Nat_bound (x : Nat) (h : x < 2 ^ 36) : fold16Nat x ≤ 15794160 := by
  unfold fold16Nat
  omega

theorem fold16Nat_twice_small (x : Nat) (h : x < 2 ^ 36) :
    fold16Nat (fold16Nat x) < 131042 := by
  have hf := fold16Nat_bound x h
  unfold fold16Nat
  omega

theorem fold16Word_nat (x : BitVec 64) (h : x.toNat < 2 ^ 36) :
    (fold16Word x).toNat = fold16Nat x.toNat := by
  have hi : (x >>> 16).toNat = x.toNat / 65536 := by
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  have hl : (x &&& 65535#64).toNat = x.toNat % 65536 := by
    simpa only [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod]
      using Nat.and_two_pow_sub_one_eq_mod x.toNat 16
  have hs : ((x >>> 16) <<< 4).toNat = 16 * (x.toNat / 65536) := by
    simp only [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, hi]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  have hp : x >>> 16 ≤ (x >>> 16) <<< 4 := by
    change (x >>> 16).toNat ≤ ((x >>> 16) <<< 4).toNat
    rw [hi, hs]; omega
  have hd : (((x >>> 16) <<< 4) - (x >>> 16)).toNat = 15 * (x.toNat / 65536) := by
    rw [BitVec.toNat_sub_of_le hp, hi, hs]
    omega
  simp only [fold16Word, BitVec.toNat_add, hl, hd, fold16Nat]
  rw [Nat.mod_eq_of_lt (by omega)]

/-- Two folds and one conditional subtraction reduce every value below 2^36.
This covers both the fixed4096 update and the proposed four-block update. -/
theorem reduce36_nat (x : BitVec 64) (h : x.toNat < 2 ^ 36) :
    (red (fold16Word (fold16Word x))).toNat = x.toNat % 65521 := by
  have h1 := fold16Word_nat x h
  have hb := fold16Nat_bound x.toNat h
  have hnext : (fold16Word x).toNat < 2 ^ 36 := by omega
  have h2 := fold16Word_nat (fold16Word x) hnext
  rw [h1] at h2
  have hs := fold16Nat_twice_small x.toNat h
  rw [red_nat _ (by omega), h2, fold16Nat_mod, fold16Nat_mod]

#print axioms reduce36_nat
end Adler32
