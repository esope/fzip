(define-generic-mode 
  'fzip-mode
  nil  ;; limitation: comments cannot start with "("
  '("let"
    "in"
    "rec"
    "import"
    "export"
    "val"
    "type" 
    "as"
    "S"
    "Pi"
    "Π"
    "sigma"
    "Σ"
    "forall"
    "∀"
    "exists"
    "∃"
    "fun"
    "λ"
    "Fun"
    "Λ"
    "nu"
    "ν"
    "open")
  '(("\\((\\*\\(.\\|\n\\|\r\\|\r\n\\)*\\*)\\)" (1 'font-lock-comment-face))
    ;; comments are between "(*" and "*)" and can contain line breaks
    ("=" . 'font-lock-operator)
    ("::" . 'font-lock-builtin)
    (":" . 'font-lock-builtin)
    ("*" . 'font-lock-operator)
    ("⋆" . 'font-lock-operator)
    ("★" . 'font-lock-operator)
    ("→" . 'font-lock-operator)
    ("->" . 'font-lock-operator)
    ("⇒" . 'font-lock-operator)
    ("=>" . 'font-lock-operator)
    ("\\." . 'font-lock-builtin)
    ("," . 'font-lock-builtin)
    ("{" . 'font-lock-builtin)
    ("}" . 'font-lock-builtin)
    ("<" . 'font-lock-builtin)
    (">" . 'font-lock-builtin)
    ("\\[" . 'font-lock-builtin)
    ("\\]" . 'font-lock-builtin)
    )
  '("\\.fzip$")           
  nil                    
  "A mode for Fzip files")

