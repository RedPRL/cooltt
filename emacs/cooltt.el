;;; cooltt.el --- Major mode for editing cooltt proofs    -*- lexical-binding: t; -*-
;;; Homepage: http://github.com/RedPRL/cooltt


;; Copyright (C) 2020  The RedPRL Development Team

;; Author: Ian Voysey <iev@cs.cmu.edu>, Jonathan Sterling <jon@jonmsterling.com>
;; Package-Requires: ((emacs "26.3"))
;; Version: 0.0.1
;; Keywords: languages

;; This program is free software; you can redistribute it and/or modify
;; it under the terms of the GNU General Public License as published by
;; the Free Software Foundation, either version 3 of the License, or

;; (at your option) any later version.

;; This program is distributed in the hope that it will be useful,
;; but WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
;; GNU General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see <http://www.gnu.org/licenses/>.

;;; Commentary:

;; This is a major mode for editing cooltt developments.  The current
;; editing features include simple syntax highlighting.  There is a command to
;; run cooltt in a compilation buffer.
;;
;; Make sure to set the variable `cooltt-command' to the location of the
;; cooltt binary.
;;
;; This file started out as a copy of redtt.el
;; (https://github.com/RedPRL/redtt/blob/master/emacs/redtt.el) and did not
;; change much.
;;
;; Unicode characters can be entered in whatever way is easiest for your
;; emacs set up; we recommend M-x set-input-mode and then selecting TeX
;; mode so that \lambda renders to λ, etc.

;;; Code:


(require 'cl-lib)
(require 'compile)

(defgroup cooltt nil "cooltt" :prefix 'cooltt :group 'languages)

(defface cooltt-declaration-keyword-face
  '((t (:inherit font-lock-keyword-face))) "Face for cooltt's declaration keywords."
  :group 'cooltt)

(defface cooltt-command-keyword-face
  '((t (:inherit font-lock-preprocessor-face))) "Face for cooltt's command keywords."
  :group 'cooltt)

(defface cooltt-number-face
  '((t (:inherit font-lock-constant-face))) "Face for cooltt's numbers."
  :group 'cooltt)

(defface cooltt-expression-keyword-face
  '((t (:inherit font-lock-builtin-face))) "Face for cooltt's expression keywords."
  :group 'cooltt)

(defface cooltt-expression-symbol-face
  '((t (:inherit font-lock-builtin-face))) "Face for cooltt's expression symbols."
  :group 'cooltt)

(defface cooltt-tactic-keyword-face
  '((t (:inherit font-lock-builtin-face))) "Face for cooltt's tactic keywords."
  :group 'cooltt)

(defface cooltt-tactic-symbol-face
  '((t (:inherit font-lock-builtin-face))) "Face for cooltt's tactic symbols."
  :group 'cooltt)

(defface cooltt-sequent-keyword-face
  '((t (:inherit font-lock-builtin-face))) "Face for cooltt's sequent keywords."
  :group 'cooltt)

(defface cooltt-sequent-symbol-face
  '((t (:inherit font-lock-builtin-face))) "Face for cooltt's sequent symbols."
  :group 'cooltt)

(defcustom cooltt-command "cooltt"
  "The command to be run for cooltt."
  :group 'cooltt
  :type 'string
  :tag "Command for cooltt"
  :options '("cooltt"))

(defcustom cooltt-debug nil
  "Is debug mode enabled for cooltt."
  :group 'cooltt
  :type 'boolean
  :local t
  :tag "Enable debug mode for cooltt")

(defcustom cooltt-options nil
  "Additional options to provide to cooltt."
  :group 'cooltt
  :type '(repeat string)
  :tag "Cooltt options")

(defvar cooltt-mode-syntax-table
  (let ((table (make-syntax-table)))
    (modify-syntax-entry ?_ "w" table)
    (modify-syntax-entry ?= "w" table)
    (modify-syntax-entry ?' "w" table)
    (modify-syntax-entry ?/  "_ 123" table)
    (modify-syntax-entry ?- ". 12" table)
    (modify-syntax-entry ?\n ">" table)
    table)
  "Syntax table for cooltt.")

(defconst cooltt-declaration-keywords
  '("def" "let" "import" "section" "lens" "export" "repack")
  "Declaration keywords.")

(defconst cooltt-command-keywords
  '("#fail" "#normalize" "#print" "#quit")
  "Command keywords.")

(defconst cooltt-expression-keywords
  '("zero" "suc" "nat" "in" "fst" "snd" "elim" "unfold" "type" "dim" "cof" "sub" "pathd" "coe" "hcom" "com" "hfill" "sig" "struct" "equation" "begin" "end")
  "Expression keywords.")


(defconst cooltt-expression-symbols
  '("=>" "|" "[" "," "*" "×" ":" "=" "_" "𝕀" "𝔽" "∂" "∧" "∨" "→" "!" "]" "->" "tt" "⊤" "ff" "⊥" "\\/" "/\\")
  "Expression symbols.")

(defconst cooltt-mode-font-lock-keywords
  `(
    ;; Declaration keyword
    (,(regexp-opt cooltt-declaration-keywords 'words) 0 'cooltt-declaration-keyword-face)
    (,(regexp-opt cooltt-command-keywords 'nil) 0 'cooltt-command-keyword-face)

    ;; Numbers
    (,(rx word-start (? "-") (+ digit)) 0 'cooltt-number-face)

    ;; Built-in expressions
    (,(regexp-opt cooltt-expression-keywords 'words) 0 'cooltt-expression-keyword-face)
    (,(regexp-opt cooltt-expression-symbols 'nil) 0 'cooltt-expression-symbol-face)
    ))


(defconst cooltt-compilation-error-regexp-alist
  `((,(concat
       "^\\([^ \n]+\\):"             ;; Filename
       "\\([0-9]+\\)\\.\\([0-9]+\\)" ;; Starting Line/Column
       "-"
       "\\([0-9]+\\)\\.\\([0-9]+\\)" ;; Ending Line/Column
       " "
       "\\(\\[Warn\\]\\)?"          ;; Match forward if we see [Warn]
       "\\(\\[Info\\]\\)?")         ;; Match forward if we see [Info]
     1 (2 . 4) (3 . 5) (6 . 7)))
  "Regexps used for matching cooltt compilation messages.
See `compilation-error-regexp-alist' for semantics.")

(define-compilation-mode cooltt-compilation-mode "Cooltt"
  "Cooltt specific `compilation-mode' derivative."
  (setq-local compilation-error-regexp-alist
              cooltt-compilation-error-regexp-alist))

(defconst cooltt--compilation-buffer-name
  "*cooltt*"
  "The name to use for cooltt compilation buffers.")

(defun cooltt--compilation-buffer-name-function (_mode)
  "Compute a buffer name for the `cooltt-mode' compilation buffer."
  cooltt--compilation-buffer-name)

(defun cooltt-toggle-debug ()
  "Toggle debug mode for cooltt."
  (interactive)
  (if cooltt-debug
      (progn
        (setq cooltt-debug nil)
        (message "Cooltt Debug Mode Disabled."))

    (setq cooltt-debug t)
    (message "Cooltt Debug Mode Enabled.")))

(defun cooltt-compile-options ()
  "Compute the options to provide to cooltt."
  (let (opts cooltt-options)
    (when cooltt-debug
      (push "--debug" opts))
    opts))

(defun cooltt-compile-buffer ()
  "Load the current file into cooltt."
  (interactive)
  (let ((filename (buffer-file-name)))
    (if filename
        (progn
          (when (buffer-modified-p) (save-buffer))
          (let* ((dir (file-name-directory filename))
                 (file (file-name-nondirectory filename))
                 (opts (mapconcat 'identity (cooltt-compile-options) " "))
                 (command (concat cooltt-command " load-file " file " " opts))

                 ;; Emacs compile config stuff - these are special vars
                 (compilation-buffer-name-function
                  'cooltt--compilation-buffer-name-function)
                 (default-directory dir))
            (compilation-start command 'cooltt-compilation-mode nil t)))
      (error "Buffer has no file name"))))

;;;###autoload
(define-derived-mode cooltt-mode prog-mode "cooltt"
  "Major mode for editing cooltt proofs.
\\{cooltt-mode-map}"

  (set (make-local-variable 'comment-start) "-- ")

  (setq font-lock-defaults '((cooltt-mode-font-lock-keywords) nil nil))

  ;; Bind mode-specific commands to keys
  (define-key cooltt-mode-map (kbd "C-c C-l") 'cooltt-compile-buffer)
  (define-key cooltt-mode-map (kbd "C-c C-x C-d") 'cooltt-toggle-debug)

  (set (make-local-variable 'completion-at-point-functions)
       '(cooltt-completion-at-point)))

;;;###autoload
(add-to-list 'auto-mode-alist '("\\.cooltt\\'" . cooltt-mode))

(provide 'cooltt)
;;; cooltt.el ends here
