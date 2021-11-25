;;; cooltt-lsp ---  -*- lexical-binding: t; -*-

;;; Commentary:
(require 'cooltt)
(require 'lsp-mode)

(lsp-register-client
 (make-lsp-client
  :new-connection (lsp-stdio-connection (list cooltt-command "-i"))
  :major-modes '(cooltt-mode)
  :server-id 'cooltt))

(lsp-consistency-check cooltt-lsp)
(add-to-list 'lsp-language-id-configuration '(cooltt-mode . "cooltt"))

;;; Code:

(provide 'cooltt-lsp)
;;; cooltt-lsp.el ends here
