" vim-cooltt ftplugin
" Language:     cooltt
" Author:       Carlo Angiuli
" Last Change:  2020 May 12

if (exists("b:did_ftplugin") || !has('job'))
  finish
endif

if (!exists('g:cooltt_path'))
  let g:cooltt_path = 'cooltt'
endif

command! Cooltt :call CheckBuffer()
nnoremap <buffer> <LocalLeader>l :call CheckBuffer()<CR>
nnoremap <buffer> <LocalLeader>p :call CheckBuffer(line('.'))<CR>
autocmd QuitPre <buffer> call s:CloseBuffer()

digraph FF 120125
digraph II 120128

" Optional argument: the last line to send to cooltt (default: all).
function! CheckBuffer(...)
  if (exists('s:job'))
    call job_stop(s:job, 'int')
  endif

  let l:current = bufname('%')

  if (!bufexists('cooltt') || (winbufnr(bufwinnr('cooltt')) != bufnr('cooltt')))
    belowright vsplit cooltt
    call s:InitBuffer()
  else
    execute bufwinnr('cooltt') . 'wincmd w'
  endif
  let b:active = l:current
  silent %d _
  wincmd p

  let s:job = job_start(g:cooltt_path .
    \' - -w ' . s:EditWidth(), {
    \'in_io': 'buffer', 'in_buf': bufnr('%'),
    \'in_bot': exists('a:1') ? a:1 : line('$'),
    \'out_io': 'buffer', 'out_name': 'cooltt', 'out_msg': 0,
    \'err_io': 'buffer', 'err_name': 'cooltt', 'err_msg': 0})
endfunction

" Call this only from cooltt output buffer.
function! g:CheckFromOutputBuffer()
  if (bufexists(b:active) && (winbufnr(bufwinnr(b:active)) == bufnr(b:active)))
    execute bufwinnr(b:active) . 'wincmd w'
    call CheckBuffer()
  endif
endfunction

function! s:InitBuffer()
  set buftype=nofile
  set syntax=cooltt
  set noswapfile
  nnoremap <buffer> <LocalLeader>l :call CheckFromOutputBuffer()<CR>
endfunction

function! s:EditWidth()
  execute bufwinnr('cooltt') . 'wincmd w'

  let l:width = winwidth(winnr())
  if (has('linebreak') && (&number || &relativenumber))
    let l:width -= &numberwidth
  endif
  if (has('folding'))
    let l:width -= &foldcolumn
  endif
  if (has('signs'))
    redir => l:signs
    silent execute 'sign place buffer=' . bufnr('%')
    redir END
    if (&signcolumn == "yes" || len(split(l:signs, "\n")) > 2)
      let l:width -= 2
    endif
  endif

  wincmd p
  return l:width
endfunction

function! s:CloseBuffer()
  if (bufexists('cooltt') && !getbufvar('cooltt', '&modified'))
    if (getbufvar('cooltt', 'active') == bufname('%'))
      bdelete cooltt
    endif
  endif
endfunction

let b:did_ftplugin = 1
