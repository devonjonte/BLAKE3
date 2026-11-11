0000000000000000 <blake3_servil_core::hasher::parent_output::<blake3_servil_core::platform::Platform>>:
       0: 48 89 f8                     	mov	rax, rdi
       3: 0f 10 06                     	movups	xmm0, xmmword ptr [rsi]
       6: 0f 10 4e 10                  	movups	xmm1, xmmword ptr [rsi + 0x10]
       a: 0f 29 4c 24 c8               	movaps	xmmword ptr [rsp - 0x38], xmm1
       f: 0f 29 44 24 b8               	movaps	xmmword ptr [rsp - 0x48], xmm0
      14: 0f 10 12                     	movups	xmm2, xmmword ptr [rdx]
      17: 0f 10 5a 10                  	movups	xmm3, xmmword ptr [rdx + 0x10]
      1b: 0f 29 54 24 d8               	movaps	xmmword ptr [rsp - 0x28], xmm2
      20: 0f 29 5c 24 e8               	movaps	xmmword ptr [rsp - 0x18], xmm3
      25: 0f 29 5f 30                  	movaps	xmmword ptr [rdi + 0x30], xmm3
      29: 0f 29 57 20                  	movaps	xmmword ptr [rdi + 0x20], xmm2
      2d: 0f 29 4f 10                  	movaps	xmmword ptr [rdi + 0x10], xmm1
      31: 0f 29 07                     	movaps	xmmword ptr [rdi], xmm0
      34: 41 80 c8 04                  	or	r8b, 0x4
      38: 0f 10 01                     	movups	xmm0, xmmword ptr [rcx]
      3b: 0f 10 49 10                  	movups	xmm1, xmmword ptr [rcx + 0x10]
      3f: 0f 29 47 40                  	movaps	xmmword ptr [rdi + 0x40], xmm0
      43: 0f 29 4f 50                  	movaps	xmmword ptr [rdi + 0x50], xmm1
      47: c6 47 60 40                  	mov	byte ptr [rdi + 0x60], 0x40
      4b: 48 c7 47 68 00 00 00 00      	mov	qword ptr [rdi + 0x68], 0x0
      53: 44 88 47 70                  	mov	byte ptr [rdi + 0x70], r8b
      57: 44 88 4f 71                  	mov	byte ptr [rdi + 0x71], r9b
      5b: c3                           	ret


0000000000000000 <<blake3_servil_core::hasher::Output<blake3_servil_core::platform::Platform>>::chaining_value>:
       0: 53                           	push	rbx
       1: 48 83 ec 20                  	sub	rsp, 0x20
       5: 48 89 fb                     	mov	rbx, rdi
       8: 0f 28 46 40                  	movaps	xmm0, xmmword ptr [rsi + 0x40]
       c: 0f 28 4e 50                  	movaps	xmm1, xmmword ptr [rsi + 0x50]
      10: 0f 29 4c 24 10               	movaps	xmmword ptr [rsp + 0x10], xmm1
      15: 0f 29 04 24                  	movaps	xmmword ptr [rsp], xmm0
      19: 0f b6 46 60                  	movzx	eax, byte ptr [rsi + 0x60]
      1d: 48 8b 4e 68                  	mov	rcx, qword ptr [rsi + 0x68]
      21: 0f b6 7e 70                  	movzx	edi, byte ptr [rsi + 0x70]
      25: 80 7e 71 05                  	cmp	byte ptr [rsi + 0x71], 0x5
      29: 75 12                        	jne	0x3d <<blake3_servil_core::hasher::Output<blake3_servil_core::platform::Platform>>::chaining_value+0x3d>
      2b: 0f b6 d0                     	movzx	edx, al
      2e: 44 0f b6 c7                  	movzx	r8d, dil
      32: 48 89 e7                     	mov	rdi, rsp
      35: ff 15 00 00 00 00            	call	qword ptr [rip]         # 0x3b <<blake3_servil_core::hasher::Output<blake3_servil_core::platform::Platform>>::chaining_value+0x3b>
		0000000000000037:  R_X86_64_GOTPCREL	blake3_servil_compress_in_place_avx512-0x4
      3b: eb 10                        	jmp	0x4d <<blake3_servil_core::hasher::Output<blake3_servil_core::platform::Platform>>::chaining_value+0x4d>
      3d: 0f b6 d0                     	movzx	edx, al
      40: 44 0f b6 c7                  	movzx	r8d, dil
      44: 48 89 e7                     	mov	rdi, rsp
      47: ff 15 00 00 00 00            	call	qword ptr [rip]         # 0x4d <<blake3_servil_core::hasher::Output<blake3_servil_core::platform::Platform>>::chaining_value+0x4d>
		0000000000000049:  R_X86_64_GOTPCREL	blake3_servil_compress_in_place_sse41-0x4
      4d: 0f 28 04 24                  	movaps	xmm0, xmmword ptr [rsp]
      51: 0f 28 4c 24 10               	movaps	xmm1, xmmword ptr [rsp + 0x10]
      56: 0f 11 4b 10                  	movups	xmmword ptr [rbx + 0x10], xmm1
      5a: 0f 11 03                     	movups	xmmword ptr [rbx], xmm0
      5d: 48 89 d8                     	mov	rax, rbx
      60: 48 83 c4 20                  	add	rsp, 0x20
      64: 5b                           	pop	rbx
      65: c3                           	ret


