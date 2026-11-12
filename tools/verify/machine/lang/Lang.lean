/-! # A small language inside Lean, with three readings

A function of the library is written once, here, as a value of `Fn`. It has
* a meaning in Lean (`Sem.lean`: an interpreter over words and bytes), which the proofs are about;
* a printer to Rust (`Fn.rust`), compiled once by us and never read by people;
* a printer to x86-64 assembly (`Fn.asm`), with no compiler in between.

Every value is a 64-bit word. Memory is reached through addresses. The language has no bounds
checks and no panics: a function's contract says what its caller owes it, and `trap` stops the
program where the contract is broken. -/

namespace L

abbrev Var := String

inductive Exp
  | const (v : Nat)
  | var (x : Var)
  /-- The address of a buffer in the function's frame. -/
  | buf (b : String)
  | add (a b : Exp)
  | sub (a b : Exp)
  | and (a b : Exp)
  | or (a b : Exp)
  | shl (a : Exp) (n : Nat)
  | shr (a : Exp) (n : Nat)
  /-- `w` bits (8, 32 or 64) at an address, zero-extended. -/
  | load (w : Nat) (addr : Exp)
  deriving Repr, Inhabited

/-- Unsigned comparisons of two words. -/
inductive Cond
  | ltu (a b : Exp)
  | eq (a b : Exp)
  | ne (a b : Exp)
  deriving Repr, Inhabited

inductive Stmt
  | set (x : Var) (e : Exp)
  /-- The low `w` bits (8, 32 or 64) of `e`, to an address. -/
  | store (w : Nat) (addr : Exp) (e : Exp)
  /-- `n` bytes (a multiple of 16) from `src` to `dst`, which do not overlap. -/
  | copy (n : Nat) (dst src : Exp)
  /-- A call of a C-ABI function of the library (a kernel), with up to six arguments, each a
      constant, a variable or a buffer's address. No result. -/
  | call (f : String) (args : List Exp)
  /-- The same call, its result kept in a variable. -/
  | callr (x : Var) (f : String) (args : List Exp)
  | ite (c : Cond) (t e : List Stmt)
  | while (c : Cond) (body : List Stmt)
  /-- The contract is broken: stop the program. -/
  | trap
  /-- One machine instruction, or a label, as its assembly text: the machine level, where the
      programmer chooses every instruction and register (kernels). A prototype's stand-in for a
      value of the machine model's own instruction type. -/
  | ins (text : String)
  deriving Repr, Inhabited

structure Fn where
  name : String
  /-- At most six, each a word (a number or an address). -/
  params : List Var
  locals : List Var
  /-- Buffers in the frame: a name and a size in bytes (a multiple of 16), 16-byte aligned. -/
  bufs : List (String × Nat)
  body : List Stmt
  ret : Exp
  /-- The C-ABI functions it calls that are not written in this language (the kernels). -/
  externs : List String
  /-- The variables to keep in registers (at most six get one); the rest live in the frame. -/
  regs : List Var := []
  /-- A kernel: its body is machine instructions; nothing is added around them. -/
  naked : Bool := false
  /-- The source returns nothing: no instruction sets a result. -/
  noResult : Bool := false
  /-- Buffers that must start on a larger boundary than 16 bytes: a name and the boundary (a power of two:
      64 for a cache line, 4096 for a page). A function with one of these sets its own frame on the
      largest such boundary; one without is laid out, and assembled, exactly as before. -/
  aligns : List (String × Nat) := []
  deriving Repr, Inhabited

/-! ## To Rust -/

def Exp.rust : Exp → String
  | .const v => s!"{v}u64"
  | .var x => x
  | .buf b => b
  | .add a b => s!"({a.rust}).wrapping_add({b.rust})"
  | .sub a b => s!"({a.rust}).wrapping_sub({b.rust})"
  | .and a b => s!"(({a.rust}) & ({b.rust}))"
  | .or a b => s!"(({a.rust}) | ({b.rust}))"
  | .shl a n => s!"(({a.rust}) << {n})"
  | .shr a n => s!"(({a.rust}) >> {n})"
  | .load 8 a => s!"(*(({a.rust}) as *const u8) as u64)"
  | .load w a => s!"(core::ptr::read_unaligned(({a.rust}) as *const u{w}) as u64)"

def Cond.rust : Cond → String
  | .ltu a b => s!"{a.rust} < {b.rust}"
  | .eq a b => s!"{a.rust} == {b.rust}"
  | .ne a b => s!"{a.rust} != {b.rust}"

mutual
  def Stmt.rust (ind : String) : Stmt → String
    | .set x e => s!"{ind}{x} = {e.rust};\n"
    | .store 8 a e => s!"{ind}*(({a.rust}) as *mut u8) = ({e.rust}) as u8;\n"
    | .store w a e => s!"{ind}core::ptr::write_unaligned(({a.rust}) as *mut u{w}, ({e.rust}) as u{w});\n"
    | .copy n d s => s!"{ind}core::ptr::copy_nonoverlapping(({s.rust}) as *const u8, ({d.rust}) as *mut u8, {n});\n"
    | .call f args => s!"{ind}{f}({", ".intercalate (args.map Exp.rust)});\n"
    | .callr x f args => s!"{ind}{x} = {f}({", ".intercalate (args.map Exp.rust)});\n"
    | .ite c t e => s!"{ind}if {c.rust} \{\n{Stmts.rust (ind ++ "    ") t}{ind}} else \{\n{Stmts.rust (ind ++ "    ") e}{ind}}\n"
    | .while c b => s!"{ind}while {c.rust} \{\n{Stmts.rust (ind ++ "    ") b}{ind}}\n"
    | .trap => s!"{ind}core::arch::asm!(\"ud2\", options(noreturn));\n"
    | .ins text => s!"{ind}compile_error!(\"a machine instruction has no Rust: {text}\");\n"
  def Stmts.rust (ind : String) : List Stmt → String
    | [] => ""
    | s :: rest => Stmt.rust ind s ++ Stmts.rust ind rest
end

/-- How many arguments each call of `f` passes (the externs are declared by it). -/
partial def arity (f : String) : List Stmt → Option Nat
  | [] => none
  | .call g args :: rest => if g == f then some args.length else arity f rest
  | .callr _ g args :: rest => if g == f then some args.length else arity f rest
  | .ite _ t e :: rest => (arity f t).orElse fun _ => (arity f e).orElse fun _ => arity f rest
  | .while _ b :: rest => (arity f b).orElse fun _ => arity f rest
  | _ :: rest => arity f rest

def Fn.rust (f : Fn) : String :=
  let params := ", ".intercalate (f.params.map fun p => s!"mut {p}: u64")
  let locals := String.join (f.locals.map fun x => s!"    let mut {x}: u64 = 0;\n")
  let bufs := String.join (f.bufs.map fun (b, n) =>
    let ty := match f.aligns.find? (·.1 == b) with
      | some (_, a) => s!"Aligned{a}"
      | none => "Aligned"
    s!"    let mut {b}_store = core::mem::MaybeUninit::<{ty}<{n}>>::uninit();\n    let {b}: u64 = {b}_store.as_mut_ptr() as u64;\n")
  s!"#[no_mangle]\n#[allow(unused_mut, unused_assignments, unused_parens, unused_variables)]\npub unsafe extern \"C\" fn {f.name}({params}) -> u64 \{\n{locals}{bufs}{Stmts.rust "    " f.body}    {f.ret.rust}\n}\n"

/-- A file of functions: no standard library, no panic machinery, nothing but the functions and the
declarations of the kernels they call. -/
def rustFile (fs : List Fn) : String :=
  let exts := (fs.flatMap fun f => f.externs.map fun g => (g, (arity g f.body).getD 0)).eraseDups
  let decl := exts.map fun (g, n) => s!"    fn {g}({", ".intercalate ((List.range n).map fun i => s!"a{i}: u64")});\n"
  "// Printed from Lean (Lang.lean). Not written or edited by hand.\n#![no_std]\n#![allow(unused_parens)]\n" ++
  "#[repr(C, align(16))]\npub struct Aligned<const N: usize>([u8; N]);\n" ++
  String.join (((fs.flatMap fun f => f.aligns.map (·.2)).eraseDups).map fun a =>
    s!"#[repr(C, align({a}))]\npub struct Aligned{a}<const N: usize>([u8; N]);\n") ++
  (if decl.isEmpty then "" else "extern \"C\" {\n" ++ String.join decl ++ "}\n") ++
  String.join ((fs.filter (!·.naked)).map Fn.rust)

/-! ## To x86-64 assembly (System V), with no compiler

Each variable has a home for the whole function: one of six registers a callee must keep, or a
slot of the frame when there are more than six. Expressions are computed in the scratch registers,
left to right. Nothing is optimised: what is written is what is emitted. -/

def homes : List String := ["rbx", "rbp", "r12", "r13", "r14", "r15"]
def temps : List String := ["rax", "rcx", "rdx", "rsi", "rdi", "r8", "r9", "r10", "r11"]
def abiArgs : List String := ["rdi", "rsi", "rdx", "rcx", "r8", "r9"]

/-- The low 32 bits and low 8 bits of a register, by name. -/
def low32 : String → String
  | "rax" => "eax" | "rcx" => "ecx" | "rdx" => "edx" | "rbx" => "ebx" | "rsi" => "esi" | "rdi" => "edi" | "rbp" => "ebp"
  | r => r ++ "d"
def low8 : String → String
  | "rax" => "al" | "rcx" => "cl" | "rdx" => "dl" | "rbx" => "bl" | "rsi" => "sil" | "rdi" => "dil" | "rbp" => "bpl"
  | r => r ++ "b"

structure Layout where
  /-- A variable's home: a register, or `qword ptr [rsp + n]`. -/
  home : Var → String
  inReg : Var → Bool
  bufAt : String → Nat
  frame : Nat
  saved : List String
  /-- The boundary the frame is set on: 16 unless a buffer asks for more. -/
  align : Nat := 16
  /-- Where the caller's RSP is kept when the frame is set on a larger boundary: `[rsp + keep]`. -/
  keep : Nat := 0

def idxOf (xs : List String) (x : String) : Nat := (xs.findIdx? (· == x)).getD 0

/-- The most arguments any call passes. -/
partial def maxArgs : List Stmt → Nat
  | [] => 0
  | .call _ args :: rest => max args.length (maxArgs rest)
  | .callr _ _ args :: rest => max args.length (maxArgs rest)
  | .ite _ t e :: rest => max (max (maxArgs t) (maxArgs e)) (maxArgs rest)
  | .while _ b :: rest => max (maxArgs b) (maxArgs rest)
  | _ :: rest => maxArgs rest

def Fn.layout (f : Fn) : Layout :=
  let all := f.params ++ f.locals
  let vars := f.regs ++ all.filter (fun x => !f.regs.contains x)
  let nreg := min vars.length homes.length
  let nslot := vars.length - nreg
  -- the frame, from RSP up: arguments a call passes on the stack (the seventh on), the buffers, the slots
  let outArgs := 8 * (maxArgs f.body - 6)
  let outArgs := if outArgs % 16 == 0 then outArgs else outArgs + 8
  -- a buffer starts on its boundary (16 unless `aligns` says more): offsets from an RSP on the largest one
  let alignOf := fun (b : String) => ((f.aligns.find? (·.1 == b)).map (·.2)).getD 16
  let align := f.aligns.foldl (fun a x => max a x.2) 16
  let bufOff := f.bufs.foldl (fun (acc : List (String × Nat) × Nat) (b, n) =>
    let at_ := (acc.2 + alignOf b - 1) / alignOf b * alignOf b
    (acc.1 ++ [(b, at_)], at_ + n)) ([], outArgs)
  let slots := bufOff.2
  let raw := slots + 8 * nslot
  -- at a call RSP must be a multiple of 16: the return address and the pushes are 8 * (1 + nreg) bytes.
  -- A frame set on a larger boundary is a multiple of 16 itself, with eight bytes for the caller's RSP.
  let frame := if align > 16 then (raw + 8 + 15) / 16 * 16
    else if (raw + 8 * (1 + nreg)) % 16 == 0 then raw else raw + 8
  { home := fun x => let i := idxOf vars x; if i < nreg then homes.getD i "" else s!"qword ptr [rsp + {slots + 8 * (i - nreg)}]"
    inReg := fun x => idxOf vars x < nreg
    bufAt := fun b => ((bufOff.1.find? (·.1 == b)).map (·.2)).getD 0
    frame := frame
    saved := homes.take nreg
    align := align
    keep := raw }

/-- A constant, a variable or a buffer's address: what an argument of a call may be. -/
def Exp.atom : Exp → Bool
  | .const _ | .var _ | .buf _ => true
  | _ => false

/-- The instructions that leave `e` in scratch register number `d`. -/
partial def Exp.asm (L : Layout) (d : Nat) : Exp → List String
  | .const v => [s!"mov {temps.getD d ""}, {v}"]
  | .var x => [s!"mov {temps.getD d ""}, {L.home x}"]
  | .buf b => [s!"lea {temps.getD d ""}, [rsp + {L.bufAt b}]"]
  | .add a b => bin L d "add" a b
  | .sub a b => bin L d "sub" a b
  | .and a b => bin L d "and" a b
  | .or a b => bin L d "or" a b
  | .shl a n => Exp.asm L d a ++ [s!"shl {temps.getD d ""}, {n}"]
  | .shr a n => Exp.asm L d a ++ [s!"shr {temps.getD d ""}, {n}"]
  | .load w a =>
    let t := temps.getD d ""
    Exp.asm L d a ++ [match w with
      | 8 => s!"movzx {low32 t}, byte ptr [{t}]"
      | 32 => s!"mov {low32 t}, dword ptr [{t}]"
      | _ => s!"mov {t}, qword ptr [{t}]"]
where
  bin (L : Layout) (d : Nat) (op : String) (a b : Exp) : List String :=
    let t := temps.getD d ""
    match b with
    | .const v => if v < 2147483648 then Exp.asm L d a ++ [s!"{op} {t}, {v}"]
                  else Exp.asm L d a ++ Exp.asm L (d + 1) b ++ [s!"{op} {t}, {temps.getD (d + 1) ""}"]
    | .var x => Exp.asm L d a ++ [s!"{op} {t}, {L.home x}"]
    | _ => Exp.asm L d a ++ Exp.asm L (d + 1) b ++ [s!"{op} {t}, {temps.getD (d + 1) ""}"]

/-- Compare, then jump to `target` when the condition is FALSE. -/
def Cond.asmUnless (L : Layout) (target : String) : Cond → List String
  | .ltu a b => Exp.asm L 0 a ++ Exp.asm L 1 b ++ ["cmp rax, rcx", s!"jae {target}"]
  | .eq a b => Exp.asm L 0 a ++ Exp.asm L 1 b ++ ["cmp rax, rcx", s!"jne {target}"]
  | .ne a b => Exp.asm L 0 a ++ Exp.asm L 1 b ++ ["cmp rax, rcx", s!"je {target}"]

/-- A call's argument, put straight into its register: a variable's home is not a scratch register,
so no argument disturbs another. -/
def argAsm (L : Layout) (reg : String) : Exp → String
  | .const v => s!"mov {reg}, {v}"
  | .var x => s!"mov {reg}, {L.home x}"
  | .buf b => s!"lea {reg}, [rsp + {L.bufAt b}]"
  | _ => "ud2"

mutual
  /-- Instructions and labels of a statement; `n` numbers the labels. -/
  partial def Stmt.asm (L : Layout) (fn : String) (n : Nat) : Stmt → List String × Nat
    | .set x e => (Exp.asm L 0 e ++ [s!"mov {L.home x}, rax"], n)
    | .store w a e =>
      (Exp.asm L 0 e ++ Exp.asm L 1 a ++ [match w with
        | 8 => "mov byte ptr [rcx], al"
        | 32 => "mov dword ptr [rcx], eax"
        | _ => "mov qword ptr [rcx], rax"], n)
    | .copy k d s =>
      (Exp.asm L 0 s ++ Exp.asm L 1 d ++
        (List.range (k / 16)).flatMap (fun i => [s!"movups xmm0, xmmword ptr [rax + {16 * i}]", s!"movups xmmword ptr [rcx + {16 * i}], xmm0"]), n)
    | .call f args =>
      -- the seventh argument on goes to the bottom of the frame (through RAX), then the six registers
      let onStack := ((args.drop 6).zipIdx).flatMap fun (a, i) => [argAsm L "rax" a, s!"mov qword ptr [rsp + {8 * i}], rax"]
      (onStack ++ (args.zip abiArgs).map (fun (a, r) => argAsm L r a) ++ [s!"call CALL({f})"], n)
    | .callr x f args =>
      let onStack := ((args.drop 6).zipIdx).flatMap fun (a, i) => [argAsm L "rax" a, s!"mov qword ptr [rsp + {8 * i}], rax"]
      (onStack ++ (args.zip abiArgs).map (fun (a, r) => argAsm L r a) ++ [s!"call CALL({f})", s!"mov {L.home x}, rax"], n)
    | .ite c t e =>
      let lelse := s!".L{fn}_{n}"; let lend := s!".L{fn}_{n + 1}"
      let (tc, n1) := Stmts.asm L fn (n + 2) t
      let (ec, n2) := Stmts.asm L fn n1 e
      (c.asmUnless L lelse ++ tc ++ [s!"jmp {lend}", lelse ++ ":"] ++ ec ++ [lend ++ ":"], n2)
    | .while c b =>
      let lhead := s!".L{fn}_{n}"; let lexit := s!".L{fn}_{n + 1}"
      let (bc, n1) := Stmts.asm L fn (n + 2) b
      ([lhead ++ ":"] ++ c.asmUnless L lexit ++ bc ++ [s!"jmp {lhead}", lexit ++ ":"], n1)
    | .trap => (["ud2"], n)
    | .ins text => ([text], n)
  partial def Stmts.asm (L : Layout) (fn : String) (n : Nat) : List Stmt → List String × Nat
    | [] => ([], n)
    | s :: rest =>
      let (a, n1) := Stmt.asm L fn n s
      let (b, n2) := Stmts.asm L fn n1 rest
      (a ++ b, n2)
end

def Fn.asm (f : Fn) : String :=
  let L := f.layout
  -- A frame on a larger boundary: RSP goes down by the frame and then to the boundary below; the caller's
  -- RSP is kept in the frame and put back at the end. Otherwise as before.
  let down := if L.align > 16 then ["mov rax, rsp", s!"sub rsp, {L.frame}", s!"and rsp, -{L.align}", s!"mov qword ptr [rsp + {L.keep}], rax"]
    else if L.frame == 0 then [] else [s!"sub rsp, {L.frame}"]
  let up := if L.align > 16 then [s!"mov rsp, qword ptr [rsp + {L.keep}]"]
    else if L.frame == 0 then [] else [s!"add rsp, {L.frame}"]
  let prologue := L.saved.map (fun r => s!"push {r}") ++ down ++
    (f.params.zip abiArgs).map (fun (p, r) => s!"mov {L.home p}, {r}")
  let (body, _) := Stmts.asm L f.name 0 f.body
  let epilogue := (if f.noResult then [] else Exp.asm L 0 f.ret) ++ up ++
    L.saved.reverse.map (fun r => s!"pop {r}") ++ ["ret"]
  let line (s : String) := if s.endsWith ":" then s ++ "\n" else "    " ++ s ++ "\n"
  s!".global {f.name}\n.global _{f.name}\n.p2align 4\n{f.name}:\n_{f.name}:\n" ++
    String.join ((if f.naked then body else prologue ++ body ++ epilogue).map line)

/-- Every call of `old` becomes a call of `new`. -/
partial def retarget (old new : String) : List Stmt → List Stmt
  | [] => []
  | .call g args :: rest => .call (if g == old then new else g) args :: retarget old new rest
  | .callr x g args :: rest => .callr x (if g == old then new else g) args :: retarget old new rest
  | .ite c t e :: rest => .ite c (retarget old new t) (retarget old new e) :: retarget old new rest
  | .while c b :: rest => .while c (retarget old new b) :: retarget old new rest
  | s :: rest => s :: retarget old new rest

/-- The functions under a prefix in place of `b3l_`, their calls of one another too, with each kernel
in `own` called in place of the symbol it replaces. -/
def rename (prefix_ : String) (own : List (String × String)) (fs : List Fn) : List Fn :=
  let pre (s : String) := if s.startsWith "b3l_" then prefix_ ++ s.drop 4 else s
  fs.map fun f =>
    let body := own.foldl (fun b (old, new) => retarget old new b) f.body
    let body := fs.foldl (fun b g => retarget g.name (pre g.name) b) body
    { f with name := pre f.name, body := (body.map fun s => match s with
        | .ins text => Stmt.ins (text.replace "b3l_" prefix_)
        | s => s) }

/-- Constants the code names: a label and its 32-bit words, 64-byte aligned. -/
def dataAsm (items : List (String × List Nat)) : String :=
  if items.isEmpty then "" else
  "#ifdef __APPLE__\n.static_data\n#else\n.section .rodata\n#endif\n" ++
  String.join (items.map fun (name, words) => s!".p2align 6\n{name}:\n" ++ String.join (words.map fun w => s!"    .long {w}\n")) ++ ".text\n"

def asmFile (fs : List Fn) (data : List (String × List Nat) := []) : String :=
  "// Printed from Lean (Lang.lean). Not written or edited by hand.\n" ++
  "#if defined(__ELF__) && defined(__linux__)\n.section .note.GNU-stack,\"\",%progbits\n#endif\n" ++
  "#ifdef __APPLE__\n#define CALL(f) _##f\n#else\n#define CALL(f) f@PLT\n#endif\n" ++
  ".intel_syntax noprefix\n" ++ dataAsm data ++ ".text\n" ++ String.join (fs.map Fn.asm)

end L
