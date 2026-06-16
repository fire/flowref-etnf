	.text
	.globl branch_select_slt
	.type branch_select_slt, @function
branch_select_slt:
	movl	%esi, %eax
	cmp	%esi, %edi
	jl	.Ltaken
	movl	%edi, %eax
.Ltaken:
	ret
	.size branch_select_slt, .-branch_select_slt
	.section .note.GNU-stack,"",@progbits
