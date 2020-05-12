# cooltt.vim

This vim plugin requires Vim 8 (released September 2016).

## Use

While editing a .cooltt file, run `:Cooltt` or `<LocalLeader>l` (`l` for `load`)
in the command (normal) mode to check the current buffer and display the output
in a separate buffer. Run `<LocalLeader>p` (`p` for `partial`) to check the
current buffer, ignoring lines below the cursor's current position.

### Typing special characters

`cooltt` uses several Unicode characters in its concrete notation; each of these
can be typed easily in the Vim mode using the `digraph` feature; alternatively,
there are ASCII equivalents.

| Char | Digraph   | ASCII |
|------|-----------|-------|
| 𝕀    | `C-k II`  | `dim` |
| 𝔽    | `C-k FF`  | `cof` |
| ∂    | `C-k dP`  |       |
| ∧    | `C-k AN`  | `/\`  |
| ∨    | `C-k OR`  | `\/`  |
| λ    | `C-k *l`  | `\`   |
| ×    | `C-k *X`  | `*`   |
| →    | `C-k ->`  | `->`  |

## Setup

This plugin is compatible with Vim 8's package system. You can (re)install it by
running the following shell command from the current directory:

    ./install.sh

If the `cooltt` binary is not in your `PATH`, add the following line to your
`.vimrc`:

    let g:cooltt_path = '/path/to/the-cooltt-binary'
