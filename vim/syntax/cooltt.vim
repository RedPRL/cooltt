" vim-cooltt syntax
" Language:     cooltt
" Author:       Carlo Angiuli, Favonia
" Last Change:  2020 May 6

if exists("b:current_syntax")
  finish
endif

setlocal iskeyword=a-z,A-Z,48-57,-,',/

syn sync minlines=50
syn sync maxlines=1000

syn match   coolttParenErr ')'
syn match   coolttBrackErr ']'
syn match   coolttBraceErr '}'

syn region  coolttEncl transparent matchgroup=coolttSymb start="(" end=")" contains=ALLBUT,coolttParenErr
syn region  coolttEncl transparent matchgroup=coolttSymb start="\[" end="\]" contains=ALLBUT,coolttBrackErr
syn region  coolttEncl transparent matchgroup=coolttSymb start="{" end="}" contains=ALLBUT,coolttBraceErr

syn match   coolttHole '?\k*'

syn keyword coolttKeyw locked unlock zero suc nat in fst snd elim unfold generalize type dim
syn keyword coolttKeyw cof sub ext coe hcom com hfill V vproj with

syn keyword coolttDecl def axiom let normalize print quit

syn match   coolttSymb '=>\|[|,*×:;=_𝕀𝔽∂∧∨¬~→]\|->\|#t\|#f'
syn match   coolttSymb '\\/\|/\\'

syn region  coolttComm excludenl start="\k\@1<!--" end="$" contains=coolttTodo
syn region  coolttComm excludenl start="\k\@1<!⍝" end="$" contains=coolttTodo
syn region  coolttBlockComm start="\k\@1<!/-" end="-/" nextgroup=coolttKeyw contains=coolttBlockComm,coolttTodo
syn keyword coolttTodo contained TODO

hi def link coolttParenErr Error
hi def link coolttBrackErr Error
hi def link coolttBraceErr Error
hi def link coolttTodo Todo
hi def link coolttHole Special
hi def link coolttKeyw Identifier
hi def link coolttDecl Statement
hi def link coolttSymb Identifier
hi def link coolttComm Comment
hi def link coolttBlockComm Comment

let b:current_syntax = "cooltt"
