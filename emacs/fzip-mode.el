;; the command to comment/uncomment text
(defun fzip-comment-dwim (arg)
"Comment or uncomment current line or region in a smart way.
For detail, see `comment-dwim'."
   (interactive "*P")
   (require 'newcomment)
   (let ((deactivate-mark nil) (comment-start "(*") (comment-end "*)"))
     (comment-dwim arg)))

;; keywords for syntax coloring
(setq myKeywords
 `(
   ( ,(regexp-opt '("let"
                    "in"
                    "rec"
                    "import"
                    "export"
                    "val"
                    "type"
                    "as"
                    "S"
                    "Pi" "Π"
                    "sigma" "Σ"
                    "forall" "∀"
                    "exists" "∃"
                    "fun" "λ"
                    "Fun" "Λ"
                    "nu" "ν"
                    "open"
                    "->" "→"
                    "=>" "⇒") 'words) . font-lock-keyword-face)
  )
)

(require 'smart-compile)

;; define the major mode.
(define-derived-mode fzip-mode fundamental-mode
"Fzip"
"fzip-mode is a major mode for editing the programming language Fzip."
  ;; make "_" be part of words
  (modify-syntax-entry ?_ "w" fzip-mode-syntax-table)
  ;; ' is part of words (for primes) and a char quote
  (modify-syntax-entry ?' "w" fzip-mode-syntax-table)
  ;; ';' is punctuation
  (modify-syntax-entry ?\; "." fzip-mode-syntax-table)
  ;; ':' is punctuation
  (modify-syntax-entry ?: "." fzip-mode-syntax-table)
  ;; '.' is punctuation
  (modify-syntax-entry ?. "." fzip-mode-syntax-table)

  (setq font-lock-defaults '(myKeywords))

  ;; modify the keymap
  (define-key fzip-mode-map [remap comment-dwim] 'fzip-comment-dwim)

  ;; OCaml style comments: “(* ... *)”
  ;; 'n' means "nested comment"
  (modify-syntax-entry ?( "(). 14n" fzip-mode-syntax-table)
  (modify-syntax-entry ?* ". 23n" fzip-mode-syntax-table)
  (modify-syntax-entry ?) "). 4n" fzip-mode-syntax-table)
  (modify-syntax-entry ?< "(>" fzip-mode-syntax-table)
  (modify-syntax-entry ?> ")" fzip-mode-syntax-table)

  (local-set-key (kbd "C-c C-c") 'compile)

)

(add-to-list 'auto-mode-alist '("\\.fzip" . fzip-mode))

;; Add the following line to your .emacs to add support for auto-complete.
;; (add-to-list 'ac-modes 'fzip-mode)

(provide 'fzip-mode)
