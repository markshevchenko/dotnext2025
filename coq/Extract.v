Require Import Arith.
Import Nat.
Require Import List.
Import ListNotations.

From Demo Require Import Payrolls.

(* === Extraction === *)
(* https://softwarefoundations.cis.upenn.edu/vfa-current/Extract.html *)
From Coq Require Extraction.
Extraction Language OCaml.

Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive nat =>
          "uint" [ "0u" "(+) 1u" ]
            "(fun zero succ n -> if n = 0u then zero () else succ (n - 1u))".
Extract Inductive prod => "( * )" [ "( , )" ].
Extract Inlined Constant fst => "fst".
Extract Inlined Constant months_in_year => "12u".
Extract Inlined Constant add => "(+)".
Extract Inlined Constant sub => "(-)".
Extract Inlined Constant mul => "(*)".
Extract Inlined Constant div => "(/)".
Extract Inlined Constant divmod => "divmod".
Extract Inlined Constant modulo => "(%)".

Recursive Extraction make_payrolls.

Set Extraction Output Directory "ocaml".
Extraction "payrolls.ml" make_payrolls.
