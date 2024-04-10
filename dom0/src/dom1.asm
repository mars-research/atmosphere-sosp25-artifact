default rel
bits 64

global _start
_start:
	lea rdi, [rel hello_string]
	mov rsi, hello_len
	mov rax, 0
	syscall
	ret

section .rodata
align 4096
hello_string:
	db "Hello from dom1!", 0
hello_len equ $ - hello_string
