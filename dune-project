(lang dune 3.17)

(name compiler)

(generate_opam_files true)

(source
 (github Maruncho/C-Toy-Compiler))

(authors "Mario Hlebarov <themariohlebarov@gmail.com>")

(maintainers "Mario Hlebarov <themariohlebarov@gmail.com>")

(license "MIT")

(documentation https://github.com/Maruncho/C-Toy-Compiler)

(package
 (name compiler)
 (synopsis "A short synopsis")
 (description "A longer description")
 (depends ocaml zarith core re)
 (tags
  ("add topics" "to describe" your project)))

; See the complete stanza docs at https://dune.readthedocs.io/en/stable/reference/dune-project/index.html
