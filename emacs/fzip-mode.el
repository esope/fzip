(require 'generic-x) ;; we need this

(define-generic-mode 
  'fzip-mode
  nil
  '("let"
    "in"
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
    "Λ")
  '(("=" . 'font-lock-builtin)
    ("::" . 'font-lock-operator)
    (":" . 'font-lock-operator)
    ("*" . 'font-lock-builtin)
    ("⋆" . 'font-lock-builtin)
    ("→" . 'font-lock-builtin)
    ("->" . 'font-lock-builtin)
    ("⇒" . 'font-lock-builtin)
    ("=>" . 'font-lock-builtin)
    ("{" . 'font-lock-delimiter-face)
    ("}" . 'font-lock-delimiter-face)
    ("[" . 'font-lock-delimiter-face)
    ("]" . 'font-lock-delimiter-face)
    ("<" . 'font-lock-delimiter-face)
    (">" . 'font-lock-delimiter-face)
    )
  '("\\.fzip$")           
  nil                    
  "A mode for Fzip files")

