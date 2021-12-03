# MiniML
A functional programming language written in OCaml

The parser to convert the external language into the internal OCaml compatible language is not my work, but everything after lines 1841 is my own implementation.
I wrote functions to evaluate expressions (using substitution of free variables), inferring the type of an expression and unifying type variables.

Lines 1 to 218 define the valid types, expressions and operations of the internal language, and showcase 10 different examples of valid external language code.

This code requires installing OCaml, see https://ocaml.org/docs/install.html

Install utop https://github.com/ocaml-community/utop

Once installed, run `utop` from the command line, and inside the utop program, run

    #use "MiniML.ml"
    execute "external MiniML code"
