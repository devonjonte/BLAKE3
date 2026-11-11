import ParentOutput
import ChainingValue
import Sse
import Avx

/-! The four functions as one program, and one lemma an instruction. Written from lift_one.py's tables. -/

set_option maxRecDepth 1000000
namespace Code
open X86

def table : List (Nat × Instr × Nat) := ParentOutput.table ++ ChainingValue.table ++ Sse.table ++ Avx.table

def prog (pc : Nat) : Option (Instr × Nat) := table.lookup pc

theorem at_10000 : prog 0x10000 = some (.mov 64 (.reg .rax) (.reg .rdi), 0x10003) := rfl
theorem at_10003 : prog 0x10003 = some (.movv false 0 (.m .rsi 0x0), 0x10006) := rfl
theorem at_10006 : prog 0x10006 = some (.movv false 1 (.m .rsi 0x10), 0x1000A) := rfl
theorem at_1000A : prog 0x1000A = some (.storev true .rsp 0xFFFFFFFFFFFFFFC8 1, 0x1000F) := rfl
theorem at_1000F : prog 0x1000F = some (.storev true .rsp 0xFFFFFFFFFFFFFFB8 0, 0x10014) := rfl
theorem at_10014 : prog 0x10014 = some (.movv false 2 (.m .rdx 0x0), 0x10017) := rfl
theorem at_10017 : prog 0x10017 = some (.movv false 3 (.m .rdx 0x10), 0x1001B) := rfl
theorem at_1001B : prog 0x1001B = some (.storev true .rsp 0xFFFFFFFFFFFFFFD8 2, 0x10020) := rfl
theorem at_10020 : prog 0x10020 = some (.storev true .rsp 0xFFFFFFFFFFFFFFE8 3, 0x10025) := rfl
theorem at_10025 : prog 0x10025 = some (.storev true .rdi 0x30 3, 0x10029) := rfl
theorem at_10029 : prog 0x10029 = some (.storev true .rdi 0x20 2, 0x1002D) := rfl
theorem at_1002D : prog 0x1002D = some (.storev true .rdi 0x10 1, 0x10031) := rfl
theorem at_10031 : prog 0x10031 = some (.storev true .rdi 0x0 0, 0x10034) := rfl
theorem at_10034 : prog 0x10034 = some (.or 8 (.reg .r8) (.imm 0x4), 0x10038) := rfl
theorem at_10038 : prog 0x10038 = some (.movv false 0 (.m .rcx 0x0), 0x1003B) := rfl
theorem at_1003B : prog 0x1003B = some (.movv false 1 (.m .rcx 0x10), 0x1003F) := rfl
theorem at_1003F : prog 0x1003F = some (.storev true .rdi 0x40 0, 0x10043) := rfl
theorem at_10043 : prog 0x10043 = some (.storev true .rdi 0x50 1, 0x10047) := rfl
theorem at_10047 : prog 0x10047 = some (.mov 8 (.mem .rdi 0x60) (.imm 0x40), 0x1004B) := rfl
theorem at_1004B : prog 0x1004B = some (.mov 64 (.mem .rdi 0x68) (.imm 0x0), 0x10053) := rfl
theorem at_10053 : prog 0x10053 = some (.mov 8 (.mem .rdi 0x70) (.reg .r8), 0x10057) := rfl
theorem at_10057 : prog 0x10057 = some (.mov 8 (.mem .rdi 0x71) (.reg .r9), 0x1005B) := rfl
theorem at_1005B : prog 0x1005B = some (.ret, 0x1005C) := rfl
theorem at_11000 : prog 0x11000 = some (.push .rbx, 0x11001) := rfl
theorem at_11001 : prog 0x11001 = some (.sub 64 (.reg .rsp) (.imm 0x20), 0x11005) := rfl
theorem at_11005 : prog 0x11005 = some (.mov 64 (.reg .rbx) (.reg .rdi), 0x11008) := rfl
theorem at_11008 : prog 0x11008 = some (.movv true 0 (.m .rsi 0x40), 0x1100C) := rfl
theorem at_1100C : prog 0x1100C = some (.movv true 1 (.m .rsi 0x50), 0x11010) := rfl
theorem at_11010 : prog 0x11010 = some (.storev true .rsp 0x10 1, 0x11015) := rfl
theorem at_11015 : prog 0x11015 = some (.storev true .rsp 0x0 0, 0x11019) := rfl
theorem at_11019 : prog 0x11019 = some (.movzx8 .rax (.mem .rsi 0x60), 0x1101D) := rfl
theorem at_1101D : prog 0x1101D = some (.mov 64 (.reg .rcx) (.mem .rsi 0x68), 0x11021) := rfl
theorem at_11021 : prog 0x11021 = some (.movzx8 .rdi (.mem .rsi 0x70), 0x11025) := rfl
theorem at_11025 : prog 0x11025 = some (.cmp 8 (.mem .rsi 0x71) (.imm 0x5), 0x11029) := rfl
theorem at_11029 : prog 0x11029 = some (.jne 0x1103D, 0x1102B) := rfl
theorem at_1102B : prog 0x1102B = some (.movzx8 .rdx (.reg .rax), 0x1102E) := rfl
theorem at_1102E : prog 0x1102E = some (.movzx8 .r8 (.reg .rdi), 0x11032) := rfl
theorem at_11032 : prog 0x11032 = some (.mov 64 (.reg .rdi) (.reg .rsp), 0x11035) := rfl
theorem at_11035 : prog 0x11035 = some (.call 0x30000, 0x1103B) := rfl
theorem at_1103B : prog 0x1103B = some (.jmp 0x1104D, 0x1103D) := rfl
theorem at_1103D : prog 0x1103D = some (.movzx8 .rdx (.reg .rax), 0x11040) := rfl
theorem at_11040 : prog 0x11040 = some (.movzx8 .r8 (.reg .rdi), 0x11044) := rfl
theorem at_11044 : prog 0x11044 = some (.mov 64 (.reg .rdi) (.reg .rsp), 0x11047) := rfl
theorem at_11047 : prog 0x11047 = some (.call 0x20000, 0x1104D) := rfl
theorem at_1104D : prog 0x1104D = some (.movv true 0 (.m .rsp 0x0), 0x11051) := rfl
theorem at_11051 : prog 0x11051 = some (.movv true 1 (.m .rsp 0x10), 0x11056) := rfl
theorem at_11056 : prog 0x11056 = some (.storev false .rbx 0x10 1, 0x1105A) := rfl
theorem at_1105A : prog 0x1105A = some (.storev false .rbx 0x0 0, 0x1105D) := rfl
theorem at_1105D : prog 0x1105D = some (.mov 64 (.reg .rax) (.reg .rbx), 0x11060) := rfl
theorem at_11060 : prog 0x11060 = some (.add 64 (.reg .rsp) (.imm 0x20), 0x11064) := rfl
theorem at_11064 : prog 0x11064 = some (.pop .rbx, 0x11065) := rfl
theorem at_11065 : prog 0x11065 = some (.ret, 0x11066) := rfl
theorem at_20000 : prog 0x20000 = some (.movv false 0 (.m .rdi 0x0), 0x20003) := rfl
theorem at_20003 : prog 0x20003 = some (.movv false 1 (.m .rdi 0x10), 0x20007) := rfl
theorem at_20007 : prog 0x20007 = some (.movv false 2 (.c 0xA54FF53A3C6EF372BB67AE856A09E667#128), 0x2000E) := rfl
theorem at_2000E : prog 0x2000E = some (.shl64 .r8 32, 0x20012) := rfl
theorem at_20012 : prog 0x20012 = some (.add 64 (.reg .rdx) (.reg .r8), 0x20015) := rfl
theorem at_20015 : prog 0x20015 = some (.movq 3 .rcx, 0x2001A) := rfl
theorem at_2001A : prog 0x2001A = some (.movq 4 .rdx, 0x2001F) := rfl
theorem at_2001F : prog 0x2001F = some (.punpcklqdq 3 (.x 4), 0x20023) := rfl
theorem at_20023 : prog 0x20023 = some (.movv false 4 (.m .rsi 0x0), 0x20026) := rfl
theorem at_20026 : prog 0x20026 = some (.movv false 5 (.m .rsi 0x10), 0x2002A) := rfl
theorem at_2002A : prog 0x2002A = some (.movv false 8 (.x 4), 0x2002E) := rfl
theorem at_2002E : prog 0x2002E = some (.shufps 4 (.x 5) 136, 0x20032) := rfl
theorem at_20032 : prog 0x20032 = some (.shufps 8 (.x 5) 221, 0x20037) := rfl
theorem at_20037 : prog 0x20037 = some (.movv false 5 (.x 8), 0x2003B) := rfl
theorem at_2003B : prog 0x2003B = some (.movv false 6 (.m .rsi 0x20), 0x2003F) := rfl
theorem at_2003F : prog 0x2003F = some (.movv false 7 (.m .rsi 0x30), 0x20043) := rfl
theorem at_20043 : prog 0x20043 = some (.movv false 8 (.x 6), 0x20047) := rfl
theorem at_20047 : prog 0x20047 = some (.shufps 6 (.x 7) 136, 0x2004B) := rfl
theorem at_2004B : prog 0x2004B = some (.pshufd 6 (.x 6) 147, 0x20050) := rfl
theorem at_20050 : prog 0x20050 = some (.shufps 8 (.x 7) 221, 0x20055) := rfl
theorem at_20055 : prog 0x20055 = some (.pshufd 7 (.x 8) 147, 0x2005B) := rfl
theorem at_2005B : prog 0x2005B = some (.movv false 14 (.c 0x0C0F0E0D080B0A090407060500030201#128), 0x20063) := rfl
theorem at_20063 : prog 0x20063 = some (.movv false 15 (.c 0x0D0C0F0E09080B0A0504070601000302#128), 0x2006B) := rfl
theorem at_2006B : prog 0x2006B = some (.mov 8 (.reg .rax) (.imm 0x7), 0x2006D) := rfl
theorem at_2006D : prog 0x2006D = some (.paddd 0 (.x 4), 0x20071) := rfl
theorem at_20071 : prog 0x20071 = some (.paddd 0 (.x 1), 0x20075) := rfl
theorem at_20075 : prog 0x20075 = some (.pxor 3 (.x 0), 0x20079) := rfl
theorem at_20079 : prog 0x20079 = some (.pshufb 3 (.x 15), 0x2007F) := rfl
theorem at_2007F : prog 0x2007F = some (.paddd 2 (.x 3), 0x20083) := rfl
theorem at_20083 : prog 0x20083 = some (.pxor 1 (.x 2), 0x20087) := rfl
theorem at_20087 : prog 0x20087 = some (.movv false 11 (.x 1), 0x2008C) := rfl
theorem at_2008C : prog 0x2008C = some (.pslld 1 20, 0x20091) := rfl
theorem at_20091 : prog 0x20091 = some (.psrld 11 12, 0x20097) := rfl
theorem at_20097 : prog 0x20097 = some (.por 1 (.x 11), 0x2009C) := rfl
theorem at_2009C : prog 0x2009C = some (.paddd 0 (.x 5), 0x200A0) := rfl
theorem at_200A0 : prog 0x200A0 = some (.paddd 0 (.x 1), 0x200A4) := rfl
theorem at_200A4 : prog 0x200A4 = some (.pxor 3 (.x 0), 0x200A8) := rfl
theorem at_200A8 : prog 0x200A8 = some (.pshufb 3 (.x 14), 0x200AE) := rfl
theorem at_200AE : prog 0x200AE = some (.paddd 2 (.x 3), 0x200B2) := rfl
theorem at_200B2 : prog 0x200B2 = some (.pxor 1 (.x 2), 0x200B6) := rfl
theorem at_200B6 : prog 0x200B6 = some (.movv false 11 (.x 1), 0x200BB) := rfl
theorem at_200BB : prog 0x200BB = some (.pslld 1 25, 0x200C0) := rfl
theorem at_200C0 : prog 0x200C0 = some (.psrld 11 7, 0x200C6) := rfl
theorem at_200C6 : prog 0x200C6 = some (.por 1 (.x 11), 0x200CB) := rfl
theorem at_200CB : prog 0x200CB = some (.pshufd 0 (.x 0) 147, 0x200D0) := rfl
theorem at_200D0 : prog 0x200D0 = some (.pshufd 3 (.x 3) 78, 0x200D5) := rfl
theorem at_200D5 : prog 0x200D5 = some (.pshufd 2 (.x 2) 57, 0x200DA) := rfl
theorem at_200DA : prog 0x200DA = some (.paddd 0 (.x 6), 0x200DE) := rfl
theorem at_200DE : prog 0x200DE = some (.paddd 0 (.x 1), 0x200E2) := rfl
theorem at_200E2 : prog 0x200E2 = some (.pxor 3 (.x 0), 0x200E6) := rfl
theorem at_200E6 : prog 0x200E6 = some (.pshufb 3 (.x 15), 0x200EC) := rfl
theorem at_200EC : prog 0x200EC = some (.paddd 2 (.x 3), 0x200F0) := rfl
theorem at_200F0 : prog 0x200F0 = some (.pxor 1 (.x 2), 0x200F4) := rfl
theorem at_200F4 : prog 0x200F4 = some (.movv false 11 (.x 1), 0x200F9) := rfl
theorem at_200F9 : prog 0x200F9 = some (.pslld 1 20, 0x200FE) := rfl
theorem at_200FE : prog 0x200FE = some (.psrld 11 12, 0x20104) := rfl
theorem at_20104 : prog 0x20104 = some (.por 1 (.x 11), 0x20109) := rfl
theorem at_20109 : prog 0x20109 = some (.paddd 0 (.x 7), 0x2010D) := rfl
theorem at_2010D : prog 0x2010D = some (.paddd 0 (.x 1), 0x20111) := rfl
theorem at_20111 : prog 0x20111 = some (.pxor 3 (.x 0), 0x20115) := rfl
theorem at_20115 : prog 0x20115 = some (.pshufb 3 (.x 14), 0x2011B) := rfl
theorem at_2011B : prog 0x2011B = some (.paddd 2 (.x 3), 0x2011F) := rfl
theorem at_2011F : prog 0x2011F = some (.pxor 1 (.x 2), 0x20123) := rfl
theorem at_20123 : prog 0x20123 = some (.movv false 11 (.x 1), 0x20128) := rfl
theorem at_20128 : prog 0x20128 = some (.pslld 1 25, 0x2012D) := rfl
theorem at_2012D : prog 0x2012D = some (.psrld 11 7, 0x20133) := rfl
theorem at_20133 : prog 0x20133 = some (.por 1 (.x 11), 0x20138) := rfl
theorem at_20138 : prog 0x20138 = some (.pshufd 0 (.x 0) 57, 0x2013D) := rfl
theorem at_2013D : prog 0x2013D = some (.pshufd 3 (.x 3) 78, 0x20142) := rfl
theorem at_20142 : prog 0x20142 = some (.pshufd 2 (.x 2) 147, 0x20147) := rfl
theorem at_20147 : prog 0x20147 = some (.decb .rax, 0x20149) := rfl
theorem at_20149 : prog 0x20149 = some (.je 0x201A5, 0x2014B) := rfl
theorem at_2014B : prog 0x2014B = some (.movv false 8 (.x 4), 0x20150) := rfl
theorem at_20150 : prog 0x20150 = some (.shufps 8 (.x 5) 214, 0x20155) := rfl
theorem at_20155 : prog 0x20155 = some (.pshufd 9 (.x 4) 15, 0x2015B) := rfl
theorem at_2015B : prog 0x2015B = some (.pshufd 4 (.x 8) 57, 0x20161) := rfl
theorem at_20161 : prog 0x20161 = some (.movv false 8 (.x 6), 0x20166) := rfl
theorem at_20166 : prog 0x20166 = some (.shufps 8 (.x 7) 250, 0x2016B) := rfl
theorem at_2016B : prog 0x2016B = some (.pblendw 9 (.x 8) 204, 0x20172) := rfl
theorem at_20172 : prog 0x20172 = some (.movv false 8 (.x 7), 0x20177) := rfl
theorem at_20177 : prog 0x20177 = some (.punpcklqdq 8 (.x 5), 0x2017C) := rfl
theorem at_2017C : prog 0x2017C = some (.pblendw 8 (.x 6) 192, 0x20183) := rfl
theorem at_20183 : prog 0x20183 = some (.pshufd 8 (.x 8) 120, 0x20189) := rfl
theorem at_20189 : prog 0x20189 = some (.punpckhdq 5 (.x 7), 0x2018D) := rfl
theorem at_2018D : prog 0x2018D = some (.punpckldq 6 (.x 5), 0x20191) := rfl
theorem at_20191 : prog 0x20191 = some (.pshufd 7 (.x 6) 30, 0x20196) := rfl
theorem at_20196 : prog 0x20196 = some (.movv false 5 (.x 9), 0x2019B) := rfl
theorem at_2019B : prog 0x2019B = some (.movv false 6 (.x 8), 0x201A0) := rfl
theorem at_201A0 : prog 0x201A0 = some (.jmp 0x2006D, 0x201A5) := rfl
theorem at_201A5 : prog 0x201A5 = some (.pxor 0 (.x 2), 0x201A9) := rfl
theorem at_201A9 : prog 0x201A9 = some (.pxor 1 (.x 3), 0x201AD) := rfl
theorem at_201AD : prog 0x201AD = some (.storev false .rdi 0x0 0, 0x201B0) := rfl
theorem at_201B0 : prog 0x201B0 = some (.storev false .rdi 0x10 1, 0x201B4) := rfl
theorem at_201B4 : prog 0x201B4 = some (.ret, 0x201B5) := rfl
theorem at_30000 : prog 0x30000 = some (.movv false 0 (.m .rdi 0x0), 0x30004) := rfl
theorem at_30004 : prog 0x30004 = some (.movv false 1 (.m .rdi 0x10), 0x30009) := rfl
theorem at_30009 : prog 0x30009 = some (.movzx8 .rax (.reg .r8), 0x3000D) := rfl
theorem at_3000D : prog 0x3000D = some (.movzx8 .rdx (.reg .rdx), 0x30010) := rfl
theorem at_30010 : prog 0x30010 = some (.shl64 .rax 32, 0x30014) := rfl
theorem at_30014 : prog 0x30014 = some (.add 64 (.reg .rdx) (.reg .rax), 0x30017) := rfl
theorem at_30017 : prog 0x30017 = some (.movq 3 .rcx, 0x3001C) := rfl
theorem at_3001C : prog 0x3001C = some (.movq 4 .rdx, 0x30021) := rfl
theorem at_30021 : prog 0x30021 = some (.vpunpcklqdq 3 3 (.x 4), 0x30025) := rfl
theorem at_30025 : prog 0x30025 = some (.movv false 2 (.c 0xA54FF53A3C6EF372BB67AE856A09E667#128), 0x3002D) := rfl
theorem at_3002D : prog 0x3002D = some (.movv false 8 (.m .rsi 0x0), 0x30031) := rfl
theorem at_30031 : prog 0x30031 = some (.movv false 9 (.m .rsi 0x10), 0x30036) := rfl
theorem at_30036 : prog 0x30036 = some (.vshufps 4 8 (.x 9) 136, 0x3003C) := rfl
theorem at_3003C : prog 0x3003C = some (.vshufps 5 8 (.x 9) 221, 0x30042) := rfl
theorem at_30042 : prog 0x30042 = some (.movv false 8 (.m .rsi 0x20), 0x30047) := rfl
theorem at_30047 : prog 0x30047 = some (.movv false 9 (.m .rsi 0x30), 0x3004C) := rfl
theorem at_3004C : prog 0x3004C = some (.vshufps 6 8 (.x 9) 136, 0x30052) := rfl
theorem at_30052 : prog 0x30052 = some (.vshufps 7 8 (.x 9) 221, 0x30058) := rfl
theorem at_30058 : prog 0x30058 = some (.pshufd 6 (.x 6) 147, 0x3005D) := rfl
theorem at_3005D : prog 0x3005D = some (.pshufd 7 (.x 7) 147, 0x30062) := rfl
theorem at_30062 : prog 0x30062 = some (.mov 8 (.reg .rax) (.imm 0x7), 0x30064) := rfl
theorem at_30064 : prog 0x30064 = some (.vpaddd 0 0 (.x 4), 0x30068) := rfl
theorem at_30068 : prog 0x30068 = some (.vpaddd 0 0 (.x 1), 0x3006C) := rfl
theorem at_3006C : prog 0x3006C = some (.vpxor 3 3 (.x 0), 0x30072) := rfl
theorem at_30072 : prog 0x30072 = some (.vprord 3 (.x 3) 16, 0x30079) := rfl
theorem at_30079 : prog 0x30079 = some (.vpaddd 2 2 (.x 3), 0x3007D) := rfl
theorem at_3007D : prog 0x3007D = some (.vpxor 1 1 (.x 2), 0x30083) := rfl
theorem at_30083 : prog 0x30083 = some (.vprord 1 (.x 1) 12, 0x3008A) := rfl
theorem at_3008A : prog 0x3008A = some (.vpaddd 0 0 (.x 5), 0x3008E) := rfl
theorem at_3008E : prog 0x3008E = some (.vpaddd 0 0 (.x 1), 0x30092) := rfl
theorem at_30092 : prog 0x30092 = some (.vpxor 3 3 (.x 0), 0x30098) := rfl
theorem at_30098 : prog 0x30098 = some (.vprord 3 (.x 3) 8, 0x3009F) := rfl
theorem at_3009F : prog 0x3009F = some (.vpaddd 2 2 (.x 3), 0x300A3) := rfl
theorem at_300A3 : prog 0x300A3 = some (.vpxor 1 1 (.x 2), 0x300A9) := rfl
theorem at_300A9 : prog 0x300A9 = some (.vprord 1 (.x 1) 7, 0x300B0) := rfl
theorem at_300B0 : prog 0x300B0 = some (.pshufd 0 (.x 0) 147, 0x300B5) := rfl
theorem at_300B5 : prog 0x300B5 = some (.pshufd 3 (.x 3) 78, 0x300BA) := rfl
theorem at_300BA : prog 0x300BA = some (.pshufd 2 (.x 2) 57, 0x300BF) := rfl
theorem at_300BF : prog 0x300BF = some (.vpaddd 0 0 (.x 6), 0x300C3) := rfl
theorem at_300C3 : prog 0x300C3 = some (.vpaddd 0 0 (.x 1), 0x300C7) := rfl
theorem at_300C7 : prog 0x300C7 = some (.vpxor 3 3 (.x 0), 0x300CD) := rfl
theorem at_300CD : prog 0x300CD = some (.vprord 3 (.x 3) 16, 0x300D4) := rfl
theorem at_300D4 : prog 0x300D4 = some (.vpaddd 2 2 (.x 3), 0x300D8) := rfl
theorem at_300D8 : prog 0x300D8 = some (.vpxor 1 1 (.x 2), 0x300DE) := rfl
theorem at_300DE : prog 0x300DE = some (.vprord 1 (.x 1) 12, 0x300E5) := rfl
theorem at_300E5 : prog 0x300E5 = some (.vpaddd 0 0 (.x 7), 0x300E9) := rfl
theorem at_300E9 : prog 0x300E9 = some (.vpaddd 0 0 (.x 1), 0x300ED) := rfl
theorem at_300ED : prog 0x300ED = some (.vpxor 3 3 (.x 0), 0x300F3) := rfl
theorem at_300F3 : prog 0x300F3 = some (.vprord 3 (.x 3) 8, 0x300FA) := rfl
theorem at_300FA : prog 0x300FA = some (.vpaddd 2 2 (.x 3), 0x300FE) := rfl
theorem at_300FE : prog 0x300FE = some (.vpxor 1 1 (.x 2), 0x30104) := rfl
theorem at_30104 : prog 0x30104 = some (.vprord 1 (.x 1) 7, 0x3010B) := rfl
theorem at_3010B : prog 0x3010B = some (.pshufd 0 (.x 0) 57, 0x30110) := rfl
theorem at_30110 : prog 0x30110 = some (.pshufd 3 (.x 3) 78, 0x30115) := rfl
theorem at_30115 : prog 0x30115 = some (.pshufd 2 (.x 2) 147, 0x3011A) := rfl
theorem at_3011A : prog 0x3011A = some (.decb .rax, 0x3011C) := rfl
theorem at_3011C : prog 0x3011C = some (.je 0x30163, 0x3011E) := rfl
theorem at_3011E : prog 0x3011E = some (.vshufps 8 4 (.x 5) 214, 0x30123) := rfl
theorem at_30123 : prog 0x30123 = some (.pshufd 9 (.x 4) 15, 0x30128) := rfl
theorem at_30128 : prog 0x30128 = some (.pshufd 4 (.x 8) 57, 0x3012E) := rfl
theorem at_3012E : prog 0x3012E = some (.vshufps 8 6 (.x 7) 250, 0x30133) := rfl
theorem at_30133 : prog 0x30133 = some (.vpblendd 9 9 (.x 8) 170, 0x30139) := rfl
theorem at_30139 : prog 0x30139 = some (.vpunpcklqdq 8 7 (.x 5), 0x3013D) := rfl
theorem at_3013D : prog 0x3013D = some (.vpblendd 8 8 (.x 6) 136, 0x30143) := rfl
theorem at_30143 : prog 0x30143 = some (.pshufd 8 (.x 8) 120, 0x30149) := rfl
theorem at_30149 : prog 0x30149 = some (.vpunpckhdq 5 5 (.x 7), 0x3014D) := rfl
theorem at_3014D : prog 0x3014D = some (.vpunpckldq 6 6 (.x 5), 0x30151) := rfl
theorem at_30151 : prog 0x30151 = some (.pshufd 7 (.x 6) 30, 0x30156) := rfl
theorem at_30156 : prog 0x30156 = some (.movv false 5 (.x 9), 0x3015A) := rfl
theorem at_3015A : prog 0x3015A = some (.movv false 6 (.x 8), 0x3015E) := rfl
theorem at_3015E : prog 0x3015E = some (.jmp 0x30064, 0x30163) := rfl
theorem at_30163 : prog 0x30163 = some (.vpxor 0 0 (.x 2), 0x30167) := rfl
theorem at_30167 : prog 0x30167 = some (.vpxor 1 1 (.x 3), 0x3016B) := rfl
theorem at_3016B : prog 0x3016B = some (.storev false .rdi 0x0 0, 0x3016F) := rfl
theorem at_3016F : prog 0x3016F = some (.storev false .rdi 0x10 1, 0x30174) := rfl
theorem at_30174 : prog 0x30174 = some (.ret, 0x30175) := rfl

end Code
