import Machine
import MemLemmas
import Code
open X86

/-! Running the program on unknown inputs. -/

namespace X86

/-- AL after a byte is put in it. -/
theorem al_of (x v : BitVec 64) : BitVec.setWidth 8 (x &&& ~~~(255 : BitVec 64) ||| v) = BitVec.setWidth 8 v := by
  bv_decide

set_option maxRecDepth 100000 in
/-- Run the instructions of a state that is written out, with facts about this state; the vector
operations and the memory's reads and writes stay as they are named. -/
macro "run_code" "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic => `(tactic|
  simp (config := {maxSteps := 100000000, implicitDefEqProofs := false}) only [steps_mk, steps_zero, step, src, X86.read, write,
    State.get, State.set, State.xmm, State.setx, trunc, al_of,
    Code.at_10000, Code.at_10003, Code.at_10006, Code.at_1000A, Code.at_1000F, Code.at_10014, Code.at_10017, Code.at_1001B, Code.at_10020, Code.at_10025, Code.at_10029, Code.at_1002D, Code.at_10031, Code.at_10034, Code.at_10038, Code.at_1003B, Code.at_1003F, Code.at_10043, Code.at_10047, Code.at_1004B, Code.at_10053, Code.at_10057, Code.at_1005B, Code.at_11000, Code.at_11001, Code.at_11005, Code.at_11008, Code.at_1100C, Code.at_11010, Code.at_11015, Code.at_11019, Code.at_1101D, Code.at_11021, Code.at_11025, Code.at_11029, Code.at_1102B, Code.at_1102E, Code.at_11032, Code.at_11035, Code.at_1103B, Code.at_1103D, Code.at_11040, Code.at_11044, Code.at_11047, Code.at_1104D, Code.at_11051, Code.at_11056, Code.at_1105A, Code.at_1105D, Code.at_11060, Code.at_11064, Code.at_11065, Code.at_20000, Code.at_20003, Code.at_20007, Code.at_2000E, Code.at_20012, Code.at_20015, Code.at_2001A, Code.at_2001F, Code.at_20023, Code.at_20026, Code.at_2002A, Code.at_2002E, Code.at_20032, Code.at_20037, Code.at_2003B, Code.at_2003F, Code.at_20043, Code.at_20047, Code.at_2004B, Code.at_20050, Code.at_20055, Code.at_2005B, Code.at_20063, Code.at_2006B, Code.at_2006D, Code.at_20071, Code.at_20075, Code.at_20079, Code.at_2007F, Code.at_20083, Code.at_20087, Code.at_2008C, Code.at_20091, Code.at_20097, Code.at_2009C, Code.at_200A0, Code.at_200A4, Code.at_200A8, Code.at_200AE, Code.at_200B2, Code.at_200B6, Code.at_200BB, Code.at_200C0, Code.at_200C6, Code.at_200CB, Code.at_200D0, Code.at_200D5, Code.at_200DA, Code.at_200DE, Code.at_200E2, Code.at_200E6, Code.at_200EC, Code.at_200F0, Code.at_200F4, Code.at_200F9, Code.at_200FE, Code.at_20104, Code.at_20109, Code.at_2010D, Code.at_20111, Code.at_20115, Code.at_2011B, Code.at_2011F, Code.at_20123, Code.at_20128, Code.at_2012D, Code.at_20133, Code.at_20138, Code.at_2013D, Code.at_20142, Code.at_20147, Code.at_20149, Code.at_2014B, Code.at_20150, Code.at_20155, Code.at_2015B, Code.at_20161, Code.at_20166, Code.at_2016B, Code.at_20172, Code.at_20177, Code.at_2017C, Code.at_20183, Code.at_20189, Code.at_2018D, Code.at_20191, Code.at_20196, Code.at_2019B, Code.at_201A0, Code.at_201A5, Code.at_201A9, Code.at_201AD, Code.at_201B0, Code.at_201B4, Code.at_30000, Code.at_30004, Code.at_30009, Code.at_3000D, Code.at_30010, Code.at_30014, Code.at_30017, Code.at_3001C, Code.at_30021, Code.at_30025, Code.at_3002D, Code.at_30031, Code.at_30036, Code.at_3003C, Code.at_30042, Code.at_30047, Code.at_3004C, Code.at_30052, Code.at_30058, Code.at_3005D, Code.at_30062, Code.at_30064, Code.at_30068, Code.at_3006C, Code.at_30072, Code.at_30079, Code.at_3007D, Code.at_30083, Code.at_3008A, Code.at_3008E, Code.at_30092, Code.at_30098, Code.at_3009F, Code.at_300A3, Code.at_300A9, Code.at_300B0, Code.at_300B5, Code.at_300BA, Code.at_300BF, Code.at_300C3, Code.at_300C7, Code.at_300CD, Code.at_300D4, Code.at_300D8, Code.at_300DE, Code.at_300E5, Code.at_300E9, Code.at_300ED, Code.at_300F3, Code.at_300FA, Code.at_300FE, Code.at_30104, Code.at_3010B, Code.at_30110, Code.at_30115, Code.at_3011A, Code.at_3011C, Code.at_3011E, Code.at_30123, Code.at_30128, Code.at_3012E, Code.at_30133, Code.at_30139, Code.at_3013D, Code.at_30143, Code.at_30149, Code.at_3014D, Code.at_30151, Code.at_30156, Code.at_3015A, Code.at_3015E, Code.at_30163, Code.at_30167, Code.at_3016B, Code.at_3016F, Code.at_30174,
    Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some, bind_pure_comp, Option.isSome_some,
    Nat.reduceEqDiff, ↓reduceIte, reduceCtorEq, BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceEq, BitVec.reduceBEq,
    BitVec.reduceAnd, BitVec.reduceSetWidth, Bool.false_eq_true, Bool.true_eq_false, Bool.false_and, Bool.true_and,
    Bool.not_true, Bool.not_false, $hs,*])

/-- What the kernels leave alone from one part to the next. -/
def Same (s s' : State) : Prop :=
  s'.rbx = s.rbx ∧ s'.rsp = s.rsp ∧ s'.rbp = s.rbp ∧ s'.rdi = s.rdi ∧ s'.r12 = s.r12 ∧ s'.r13 = s.r13 ∧ s'.r14 = s.r14 ∧
    s'.r15 = s.r15 ∧ s'.mem = s.mem

theorem Same.trans {a b c : State} (h : Same a b) (k : Same b c) : Same a c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  obtain ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩ := k
  exact ⟨k1.trans h1, k2.trans h2, k3.trans h3, k4.trans h4, k5.trans h5, k6.trans h6, k7.trans h7, k8.trans h8, k9.trans h9⟩

end X86
