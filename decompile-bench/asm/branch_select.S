	.text
	.globl branch_select
	.type branch_select, @function
branch_select:
	movl	%esi, %eax
	cmp	%esi, %edi
	jb	.Ltaken
	movl	%edi, %eax
.Ltaken:
	ret
	.size branch_select, .-branch_select
	.section .note.GNU-stack,"",@progbits
