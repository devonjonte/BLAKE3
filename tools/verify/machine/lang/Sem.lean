import Lang

/-! # What a program of the language means

An interpreter in Lean: the definition the proofs are about. A state is the variables, the memory
and what an observer has seen (every address read or written and every branch's way). A call of a
kernel is whatever the environment says it does to memory: the kernel's contract. `none` is a trap,
or the fuel running out. -/

namespace L

abbrev Word := BitVec 64
abbrev Mem := Word → BitVec 8

/-- What timing and the cache can show: an address touched, or which way a branch went. -/
inductive Obs
  | addr (a : Word)
  | branch (taken : Bool)
  deriving Repr, DecidableEq

structure St where
  vars : Var → Word
  mem : Mem
  seen : List Obs

/-- `w` bits (8, 32 or 64) at `a`, little-endian, zero-extended. -/
def Mem.rd (m : Mem) (w : Nat) (a : Word) : Word :=
  match w with
  | 8 => (m a).setWidth 64
  | 32 => (m (a + 3) ++ m (a + 2) ++ m (a + 1) ++ m a).setWidth 64
  | _ => m (a + 7) ++ m (a + 6) ++ m (a + 5) ++ m (a + 4) ++ m (a + 3) ++ m (a + 2) ++ m (a + 1) ++ m a

/-- The low `w` bits of `v`, to `a`. -/
def Mem.wr (m : Mem) (w : Nat) (a v : Word) : Mem := fun x =>
  if (x - a).toNat < w / 8 then (v >>> (8 * (x - a).toNat)).setWidth 8 else m x

/-- `n` bytes from `src` to `dst`. -/
def Mem.cp (m : Mem) (n : Nat) (dst src : Word) : Mem := fun x =>
  if (x - dst).toNat < n then m (src + (x - dst)) else m x

structure Env where
  /-- Where each buffer of the frame is. -/
  buf : String → Word
  /-- A kernel's contract: what a call with these arguments does to memory (`none`: its
      precondition does not hold). -/
  ext : String → List Word → Mem → Option Mem

def Exp.eval (E : Env) (s : St) : Exp → Word
  | .const v => BitVec.ofNat 64 v
  | .var x => s.vars x
  | .buf b => E.buf b
  | .add a b => a.eval E s + b.eval E s
  | .sub a b => a.eval E s - b.eval E s
  | .and a b => a.eval E s &&& b.eval E s
  | .or a b => a.eval E s ||| b.eval E s
  | .shl a n => a.eval E s <<< n
  | .shr a n => a.eval E s >>> n
  | .load w a => s.mem.rd w (a.eval E s)

/-- The addresses an expression loads from, innermost first. -/
def Exp.loads (E : Env) (s : St) : Exp → List Obs
  | .const _ | .var _ | .buf _ => []
  | .add a b | .sub a b | .and a b | .or a b => a.loads E s ++ b.loads E s
  | .shl a _ | .shr a _ => a.loads E s
  | .load _ a => a.loads E s ++ [.addr (a.eval E s)]

def Cond.eval (E : Env) (s : St) : Cond → Bool
  | .ltu a b => (a.eval E s).ult (b.eval E s)
  | .eq a b => a.eval E s == b.eval E s
  | .ne a b => a.eval E s != b.eval E s

def Cond.loads (E : Env) (s : St) : Cond → List Obs
  | .ltu a b | .eq a b | .ne a b => a.loads E s ++ b.loads E s

def St.see (s : St) (o : List Obs) : St := { s with seen := o.reverse ++ s.seen }

/-- Run statements: at most `fuel` steps. -/
def exec (E : Env) : Nat → List Stmt → St → Option St
  | _, [], s => some s
  | 0, _ :: _, _ => none
  | fuel + 1, st :: rest, s =>
    match st with
    | .set x e =>
      let v := e.eval E s
      exec E fuel rest { (s.see (e.loads E s)) with vars := fun y => if y = x then v else s.vars y }
    | .store w a e =>
      let s' := s.see (e.loads E s ++ a.loads E s ++ [.addr (a.eval E s)])
      exec E fuel rest { s' with mem := s.mem.wr w (a.eval E s) (e.eval E s) }
    | .copy n d src =>
      let s' := s.see (src.loads E s ++ d.loads E s ++ [.addr (src.eval E s), .addr (d.eval E s)])
      exec E fuel rest { s' with mem := s.mem.cp n (d.eval E s) (src.eval E s) }
    | .call f args =>
      match E.ext f (args.map (·.eval E s)) s.mem with
      | none => none
      | some m => exec E fuel rest { s with mem := m }
    | .ite c t e =>
      let b := c.eval E s
      (exec E fuel (if b then t else e) (s.see (c.loads E s ++ [.branch b]))).bind (exec E fuel rest)
    | .while c body =>
      let b := c.eval E s
      let s' := s.see (c.loads E s ++ [.branch b])
      if b then (exec E fuel body s').bind (exec E fuel (st :: rest)) else exec E fuel rest s'
    | .trap => none
    -- A machine instruction's meaning is the machine model's; this interpreter has none for it yet.
    | .ins _ => none

/-- A call of `f`: the parameters get the arguments, the locals zero. The result and the state. -/
def Fn.run (E : Env) (fuel : Nat) (f : Fn) (args : List Word) (m : Mem) : Option (Word × St) :=
  let vars : Var → Word := fun x => ((f.params.zip args).lookup x).getD 0
  (exec E fuel f.body { vars, mem := m, seen := [] }).map fun s => (f.ret.eval E s, s)

end L
